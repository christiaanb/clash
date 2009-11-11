{-# LANGUAGE PackageImports #-}
--
-- Functions to bring a Core expression in normal form. This module provides a
-- top level function "normalize", and defines the actual transformation passes that
-- are performed.
--
module CLasH.Normalize (getNormalized, normalizeExpr, splitNormalized) where

-- Standard modules
import Debug.Trace
import qualified Maybe
import qualified List
import qualified "transformers" Control.Monad.Trans as Trans
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Writer as Writer
import qualified Data.Map as Map
import qualified Data.Monoid as Monoid
import Data.Accessor

-- GHC API
import CoreSyn
import qualified UniqSupply
import qualified CoreUtils
import qualified Type
import qualified TcType
import qualified Name
import qualified Id
import qualified Var
import qualified VarSet
import qualified NameSet
import qualified CoreFVs
import qualified CoreUtils
import qualified MkCore
import qualified HscTypes
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import CLasH.Normalize.NormalizeTypes
import CLasH.Translator.TranslatorTypes
import CLasH.Normalize.NormalizeTools
import CLasH.VHDL.VHDLTypes
import qualified CLasH.Utils as Utils
import CLasH.Utils.Core.CoreTools
import CLasH.Utils.Core.BinderTools
import CLasH.Utils.Pretty

--------------------------------
-- Start of transformations
--------------------------------

--------------------------------
-- η abstraction
--------------------------------
eta, etatop :: Transform
eta expr | is_fun expr && not (is_lam expr) = do
  let arg_ty = (fst . Type.splitFunTy . CoreUtils.exprType) expr
  id <- Trans.lift $ mkInternalVar "param" arg_ty
  change (Lam id (App expr (Var id)))
-- Leave all other expressions unchanged
eta e = return e
etatop = notappargs ("eta", eta)

--------------------------------
-- β-reduction
--------------------------------
beta, betatop :: Transform
-- Substitute arg for x in expr. For value lambda's, also clone before
-- substitution.
beta (App (Lam x expr) arg) | CoreSyn.isTyVar x = setChanged >> substitute x arg expr
                            | otherwise      = setChanged >> substitute_clone x arg expr
-- Propagate the application into the let
beta (App (Let binds expr) arg) = change $ Let binds (App expr arg)
-- Propagate the application into each of the alternatives
beta (App (Case scrut b ty alts) arg) = change $ Case scrut b ty' alts'
  where 
    alts' = map (\(con, bndrs, expr) -> (con, bndrs, (App expr arg))) alts
    ty' = CoreUtils.applyTypeToArg ty arg
-- Leave all other expressions unchanged
beta expr = return expr
-- Perform this transform everywhere
betatop = everywhere ("beta", beta)

--------------------------------
-- Cast propagation
--------------------------------
-- Try to move casts as much downward as possible.
castprop, castproptop :: Transform
castprop (Cast (Let binds expr) ty) = change $ Let binds (Cast expr ty)
castprop expr@(Cast (Case scrut b _ alts) ty) = change (Case scrut b ty alts')
  where
    alts' = map (\(con, bndrs, expr) -> (con, bndrs, (Cast expr ty))) alts
-- Leave all other expressions unchanged
castprop expr = return expr
-- Perform this transform everywhere
castproptop = everywhere ("castprop", castprop)

--------------------------------
-- Cast simplification. Mostly useful for state packing and unpacking, but
-- perhaps for others as well.
--------------------------------
castsimpl, castsimpltop :: Transform
castsimpl expr@(Cast val ty) = do
  -- Don't extract values that are already simpl
  local_var <- Trans.lift $ is_local_var val
  -- Don't extract values that are not representable, to prevent loops with
  -- inlinenonrep
  repr <- isRepr val
  if (not local_var) && repr
    then do
      -- Generate a binder for the expression
      id <- Trans.lift $ mkBinderFor val "castval"
      -- Extract the expression
      change $ Let (NonRec id val) (Cast (Var id) ty)
    else
      return expr
-- Leave all other expressions unchanged
castsimpl expr = return expr
-- Perform this transform everywhere
castsimpltop = everywhere ("castsimpl", castsimpl)


--------------------------------
-- Lambda simplication
--------------------------------
-- Ensure that a lambda always evaluates to a let expressions or a simple
-- variable reference.
lambdasimpl, lambdasimpltop :: Transform
-- Don't simplify a lambda that evaluates to let, since this is already
-- normal form (and would cause infinite loops).
lambdasimpl expr@(Lam _ (Let _ _)) = return expr
-- Put the of a lambda in its own binding, but not when the expression is
-- already a local variable, or not representable (to prevent loops with
-- inlinenonrep).
lambdasimpl expr@(Lam bndr res) = do
  repr <- isRepr res
  local_var <- Trans.lift $ is_local_var res
  if not local_var && repr
    then do
      id <- Trans.lift $ mkBinderFor res "res"
      change $ Lam bndr (Let (NonRec id res) (Var id))
    else
      -- If the result is already a local var or not representable, don't
      -- extract it.
      return expr

-- Leave all other expressions unchanged
lambdasimpl expr = return expr
-- Perform this transform everywhere
lambdasimpltop = everywhere ("lambdasimpl", lambdasimpl)

--------------------------------
-- let derecursification
--------------------------------
letderec, letderectop :: Transform
letderec expr@(Let (Rec binds) res) = case liftable of
  -- Nothing is liftable, just return
  [] -> return expr
  -- Something can be lifted, generate a new let expression
  _ -> change $ mkNonRecLets liftable (Let (Rec nonliftable) res)
  where
    -- Make a list of all the binders bound in this recursive let
    bndrs = map fst binds
    -- See which bindings are liftable
    (liftable, nonliftable) = List.partition canlift binds
    -- Any expression that does not use any of the binders in this recursive let
    -- can be lifted into a nonrec let. It can't use its own binder either,
    -- since that would mean the binding is self-recursive and should be in a
    -- single bind recursive let.
    canlift (bndr, e) = not $ expr_uses_binders bndrs e
-- Leave all other expressions unchanged
letderec expr = return expr
-- Perform this transform everywhere
letderectop = everywhere ("letderec", letderec)

--------------------------------
-- let simplification
--------------------------------
letsimpl, letsimpltop :: Transform
-- Don't simplify a let that evaluates to another let, since this is already
-- normal form (and would cause infinite loops with letflat below).
letsimpl expr@(Let _ (Let _ _)) = return expr
-- Put the "in ..." value of a let in its own binding, but not when the
-- expression is already a local variable, or not representable (to prevent loops with inlinenonrep).
letsimpl expr@(Let binds res) = do
  repr <- isRepr res
  local_var <- Trans.lift $ is_local_var res
  if not local_var && repr
    then do
      -- If the result is not a local var already (to prevent loops with
      -- ourselves), extract it.
      id <- Trans.lift $ mkBinderFor res "foo"
      change $ Let binds (Let (NonRec id  res) (Var id))
    else
      -- If the result is already a local var, don't extract it.
      return expr

-- Leave all other expressions unchanged
letsimpl expr = return expr
-- Perform this transform everywhere
letsimpltop = everywhere ("letsimpl", letsimpl)

--------------------------------
-- let flattening
--------------------------------
-- Takes a let that binds another let, and turns that into two nested lets.
-- e.g., from:
-- let b = (let b' = expr' in res') in res
-- to:
-- let b' = expr' in (let b = res' in res)
letflat, letflattop :: Transform
-- Turn a nonrec let that binds a let into two nested lets.
letflat (Let (NonRec b (Let binds  res')) res) = 
  change $ Let binds (Let (NonRec b res') res)
letflat (Let (Rec binds) expr) = do
  -- Flatten each binding.
  binds' <- Utils.concatM $ Monad.mapM flatbind binds
  -- Return the new let. We don't use change here, since possibly nothing has
  -- changed. If anything has changed, flatbind has already flagged that
  -- change.
  return $ Let (Rec binds') expr
  where
    -- Turns a binding of a let into a multiple bindings, or any other binding
    -- into a list with just that binding
    flatbind :: (CoreBndr, CoreExpr) -> TransformMonad [(CoreBndr, CoreExpr)]
    flatbind (b, Let (Rec binds) expr) = change ((b, expr):binds)
    flatbind (b, Let (NonRec b' expr') expr) = change [(b, expr), (b', expr')]
    flatbind (b, expr) = return [(b, expr)]
-- Leave all other expressions unchanged
letflat expr = return expr
-- Perform this transform everywhere
letflattop = everywhere ("letflat", letflat)

--------------------------------
-- empty let removal
--------------------------------
-- Remove empty (recursive) lets
letremove, letremovetop :: Transform
letremove (Let (Rec []) res) = change $ res
-- Leave all other expressions unchanged
letremove expr = return expr
-- Perform this transform everywhere
letremovetop = everywhere ("letremove", letremove)

--------------------------------
-- Simple let binding removal
--------------------------------
-- Remove a = b bindings from let expressions everywhere
letremovesimpletop :: Transform
letremovesimpletop = everywhere ("letremovesimple", inlinebind (\(b, e) -> Trans.lift $ is_local_var e))

--------------------------------
-- Unused let binding removal
--------------------------------
letremoveunused, letremoveunusedtop :: Transform
letremoveunused expr@(Let (NonRec b bound) res) = do
  let used = expr_uses_binders [b] res
  if used
    then return expr
    else change res
letremoveunused expr@(Let (Rec binds) res) = do
  -- Filter out all unused binds.
  let binds' = filter dobind binds
  -- Only set the changed flag if binds got removed
  changeif (length binds' /= length binds) (Let (Rec binds') res)
    where
      bound_exprs = map snd binds
      -- For each bind check if the bind is used by res or any of the bound
      -- expressions
      dobind (bndr, _) = any (expr_uses_binders [bndr]) (res:bound_exprs)
-- Leave all other expressions unchanged
letremoveunused expr = return expr
letremoveunusedtop = everywhere ("letremoveunused", letremoveunused)

{-
--------------------------------
-- Identical let binding merging
--------------------------------
-- Merge two bindings in a let if they are identical 
-- TODO: We would very much like to use GHC's CSE module for this, but that
-- doesn't track if something changed or not, so we can't use it properly.
letmerge, letmergetop :: Transform
letmerge expr@(Let _ _) = do
  let (binds, res) = flattenLets expr
  binds' <- domerge binds
  return $ mkNonRecLets binds' res
  where
    domerge :: [(CoreBndr, CoreExpr)] -> TransformMonad [(CoreBndr, CoreExpr)]
    domerge [] = return []
    domerge (e:es) = do 
      es' <- mapM (mergebinds e) es
      es'' <- domerge es'
      return (e:es'')

    -- Uses the second bind to simplify the second bind, if applicable.
    mergebinds :: (CoreBndr, CoreExpr) -> (CoreBndr, CoreExpr) -> TransformMonad (CoreBndr, CoreExpr)
    mergebinds (b1, e1) (b2, e2)
      -- Identical expressions? Replace the second binding with a reference to
      -- the first binder.
      | CoreUtils.cheapEqExpr e1 e2 = change $ (b2, Var b1)
      -- Different expressions? Don't change
      | otherwise = return (b2, e2)
-- Leave all other expressions unchanged
letmerge expr = return expr
letmergetop = everywhere ("letmerge", letmerge)
-}

--------------------------------
-- Non-representable binding inlining
--------------------------------
-- Remove a = B bindings, with B of a non-representable type, from let
-- expressions everywhere. This means that any value that we can't generate a
-- signal for, will be inlined and hopefully turned into something we can
-- represent.
--
-- This is a tricky function, which is prone to create loops in the
-- transformations. To fix this, we make sure that no transformation will
-- create a new let binding with a non-representable type. These other
-- transformations will just not work on those function-typed values at first,
-- but the other transformations (in particular β-reduction) should make sure
-- that the type of those values eventually becomes representable.
inlinenonreptop :: Transform
inlinenonreptop = everywhere ("inlinenonrep", inlinebind ((Monad.liftM not) . isRepr . snd))

--------------------------------
-- Top level function inlining
--------------------------------
-- This transformation inlines top level bindings that have been generated by
-- the compiler and are really simple. Really simple currently means that the
-- normalized form only contains a single binding, which catches most of the
-- cases where a top level function is created that simply calls a type class
-- method with a type and dictionary argument, e.g.
--   fromInteger = GHC.Num.fromInteger (SizedWord D8) $dNum
-- which is later called using simply
--   fromInteger (smallInteger 10)
-- By inlining such calls to simple, compiler generated functions, we prevent
-- huge amounts of trivial components in the VHDL output, which the user never
-- wanted. We never inline user-defined functions, since we want to preserve
-- all structure defined by the user. Currently this includes all functions
-- that were created by funextract, since we would get loops otherwise.
--
-- Note that "defined by the compiler" isn't completely watertight, since GHC
-- doesn't seem to set all those names as "system names", we apply some
-- guessing here.
inlinetoplevel, inlinetopleveltop :: Transform
-- Any system name is candidate for inlining. Never inline user-defined
-- functions, to preserve structure.
inlinetoplevel expr@(Var f) | not $ isUserDefined f = do
  norm <- isNormalizeable f
  -- See if this is a top level binding for which we have a body
  body_maybe <- Trans.lift $ getGlobalBind f
  if norm && Maybe.isJust body_maybe
    then do
      -- Get the normalized version
      norm <- Trans.lift $ getNormalized f
      if needsInline norm 
        then do
          -- Regenerate all uniques in the to-be-inlined expression
          norm_uniqued <- Trans.lift $ genUniques norm
          change norm_uniqued
        else
          return expr
    else
      -- No body or not normalizeable.
      return expr
-- Leave all other expressions unchanged
inlinetoplevel expr = return expr
inlinetopleveltop = everywhere ("inlinetoplevel", inlinetoplevel)

needsInline :: CoreExpr -> Bool
needsInline expr = case splitNormalized expr of
  -- Inline any function that only has a single definition, it is probably
  -- simple enough. This might inline some stuff that it shouldn't though it
  -- will never inline user-defined functions (inlinetoplevel only tries
  -- system names) and inlining should never break things.
  (args, [bind], res) -> True
  _ -> False

--------------------------------
-- Scrutinee simplification
--------------------------------
scrutsimpl,scrutsimpltop :: Transform
-- Don't touch scrutinees that are already simple
scrutsimpl expr@(Case (Var _) _ _ _) = return expr
-- Replace all other cases with a let that binds the scrutinee and a new
-- simple scrutinee, but only when the scrutinee is representable (to prevent
-- loops with inlinenonrep, though I don't think a non-representable scrutinee
-- will be supported anyway...) 
scrutsimpl expr@(Case scrut b ty alts) = do
  repr <- isRepr scrut
  if repr
    then do
      id <- Trans.lift $ mkBinderFor scrut "scrut"
      change $ Let (NonRec id scrut) (Case (Var id) b ty alts)
    else
      return expr
-- Leave all other expressions unchanged
scrutsimpl expr = return expr
-- Perform this transform everywhere
scrutsimpltop = everywhere ("scrutsimpl", scrutsimpl)

--------------------------------
-- Scrutinee binder removal
--------------------------------
-- A case expression can have an extra binder, to which the scrutinee is bound
-- after bringing it to WHNF. This is used for forcing evaluation of strict
-- arguments. Since strictness does not matter for us (rather, everything is
-- sort of strict), this binder is ignored when generating VHDL, and must thus
-- be wild in the normal form.
scrutbndrremove, scrutbndrremovetop :: Transform
-- If the scrutinee is already simple, and the bndr is not wild yet, replace
-- all occurences of the binder with the scrutinee variable.
scrutbndrremove (Case (Var scrut) bndr ty alts) | bndr_used = do
    alts' <- mapM subs_bndr alts
    return $ Case (Var scrut) wild ty alts'
  where
    is_used (_, _, expr) = expr_uses_binders [bndr] expr
    bndr_used = or $ map is_used alts
    subs_bndr (con, bndrs, expr) = do
      expr' <- substitute bndr (Var scrut) expr
      return (con, bndrs, expr')
    wild = MkCore.mkWildBinder (Id.idType bndr)
scrutbndrremovetop = everywhere ("scrutbndrremove", scrutbndrremove)

--------------------------------
-- Case binder wildening
--------------------------------
casesimpl, casesimpltop :: Transform
-- This is already a selector case (or, if x does not appear in bndrs, a very
-- simple case statement that will be removed by caseremove below). Just leave
-- it be.
casesimpl expr@(Case scrut b ty [(con, bndrs, Var x)]) = return expr
-- Make sure that all case alternatives have only wild binders and simple
-- expressions.
-- This is done by creating a new let binding for each non-wild binder, which
-- is bound to a new simple selector case statement and for each complex
-- expression. We do this only for representable types, to prevent loops with
-- inlinenonrep.
casesimpl expr@(Case scrut b ty alts) = do
  (bindingss, alts') <- (Monad.liftM unzip) $ mapM doalt alts
  let bindings = concat bindingss
  -- Replace the case with a let with bindings and a case
  let newlet = mkNonRecLets bindings (Case scrut b ty alts')
  -- If there are no non-wild binders, or this case is already a simple
  -- selector (i.e., a single alt with exactly one binding), already a simple
  -- selector altan no bindings (i.e., no wild binders in the original case),
  -- don't change anything, otherwise, replace the case.
  if null bindings then return expr else change newlet 
  where
  -- Generate a single wild binder, since they are all the same
  wild = MkCore.mkWildBinder
  -- Wilden the binders of one alt, producing a list of bindings as a
  -- sideeffect.
  doalt :: CoreAlt -> TransformMonad ([(CoreBndr, CoreExpr)], CoreAlt)
  doalt (con, bndrs, expr) = do
    -- Make each binder wild, if possible
    bndrs_res <- Monad.zipWithM dobndr bndrs [0..]
    let (newbndrs, bindings_maybe) = unzip bndrs_res
    -- Extract a complex expression, if possible. For this we check if any of
    -- the new list of bndrs are used by expr. We can't use free_vars here,
    -- since that looks at the old bndrs.
    let uses_bndrs = not $ VarSet.isEmptyVarSet $ CoreFVs.exprSomeFreeVars (`elem` newbndrs) $ expr
    (exprbinding_maybe, expr') <- doexpr expr uses_bndrs
    -- Create a new alternative
    let newalt = (con, newbndrs, expr')
    let bindings = Maybe.catMaybes (bindings_maybe ++ [exprbinding_maybe])
    return (bindings, newalt)
    where
      -- Make wild alternatives for each binder
      wildbndrs = map (\bndr -> MkCore.mkWildBinder (Id.idType bndr)) bndrs
      -- A set of all the binders that are used by the expression
      free_vars = CoreFVs.exprSomeFreeVars (`elem` bndrs) expr
      -- Look at the ith binder in the case alternative. Return a new binder
      -- for it (either the same one, or a wild one) and optionally a let
      -- binding containing a case expression.
      dobndr :: CoreBndr -> Int -> TransformMonad (CoreBndr, Maybe (CoreBndr, CoreExpr))
      dobndr b i = do
        repr <- isRepr b
        -- Is b wild (e.g., not a free var of expr. Since b is only in scope
        -- in expr, this means that b is unused if expr does not use it.)
        let wild = not (VarSet.elemVarSet b free_vars)
        -- Create a new binding for any representable binder that is not
        -- already wild and is representable (to prevent loops with
        -- inlinenonrep).
        if (not wild) && repr
          then do
            -- Create on new binder that will actually capture a value in this
            -- case statement, and return it.
            let bty = (Id.idType b)
            id <- Trans.lift $ mkInternalVar "sel" bty
            let binders = take i wildbndrs ++ [id] ++ drop (i+1) wildbndrs
            let caseexpr = Case scrut b bty [(con, binders, Var id)]
            return (wildbndrs!!i, Just (b, caseexpr))
          else 
            -- Just leave the original binder in place, and don't generate an
            -- extra selector case.
            return (b, Nothing)
      -- Process the expression of a case alternative. Accepts an expression
      -- and whether this expression uses any of the binders in the
      -- alternative. Returns an optional new binding and a new expression.
      doexpr :: CoreExpr -> Bool -> TransformMonad (Maybe (CoreBndr, CoreExpr), CoreExpr)
      doexpr expr uses_bndrs = do
        local_var <- Trans.lift $ is_local_var expr
        repr <- isRepr expr
        -- Extract any expressions that do not use any binders from this
        -- alternative, is not a local var already and is representable (to
        -- prevent loops with inlinenonrep).
        if (not uses_bndrs) && (not local_var) && repr
          then do
            id <- Trans.lift $ mkBinderFor expr "caseval"
            -- We don't flag a change here, since casevalsimpl will do that above
            -- based on Just we return here.
            return $ (Just (id, expr), Var id)
          else
            -- Don't simplify anything else
            return (Nothing, expr)
-- Leave all other expressions unchanged
casesimpl expr = return expr
-- Perform this transform everywhere
casesimpltop = everywhere ("casesimpl", casesimpl)

--------------------------------
-- Case removal
--------------------------------
-- Remove case statements that have only a single alternative and only wild
-- binders.
caseremove, caseremovetop :: Transform
-- Replace a useless case by the value of its single alternative
caseremove (Case scrut b ty [(con, bndrs, expr)]) | not usesvars = change expr
    -- Find if any of the binders are used by expr
    where usesvars = (not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` bndrs))) expr
-- Leave all other expressions unchanged
caseremove expr = return expr
-- Perform this transform everywhere
caseremovetop = everywhere ("caseremove", caseremove)

--------------------------------
-- Argument extraction
--------------------------------
-- Make sure that all arguments of a representable type are simple variables.
appsimpl, appsimpltop :: Transform
-- Simplify all representable arguments. Do this by introducing a new Let
-- that binds the argument and passing the new binder in the application.
appsimpl expr@(App f arg) = do
  -- Check runtime representability
  repr <- isRepr arg
  local_var <- Trans.lift $ is_local_var arg
  if repr && not local_var
    then do -- Extract representable arguments
      id <- Trans.lift $ mkBinderFor arg "arg"
      change $ Let (NonRec id arg) (App f (Var id))
    else -- Leave non-representable arguments unchanged
      return expr
-- Leave all other expressions unchanged
appsimpl expr = return expr
-- Perform this transform everywhere
appsimpltop = everywhere ("appsimpl", appsimpl)

--------------------------------
-- Function-typed argument propagation
--------------------------------
-- Remove all applications to function-typed arguments, by duplication the
-- function called with the function-typed parameter replaced by the free
-- variables of the argument passed in.
argprop, argproptop :: Transform
-- Transform any application of a named function (i.e., skip applications of
-- lambda's). Also skip applications that have arguments with free type
-- variables, since we can't inline those.
argprop expr@(App _ _) | is_var fexpr = do
  -- Find the body of the function called
  body_maybe <- Trans.lift $ getGlobalBind f
  case body_maybe of
    Just body -> do
      -- Process each of the arguments in turn
      (args', changed) <- Writer.listen $ mapM doarg args
      -- See if any of the arguments changed
      case Monoid.getAny changed of
        True -> do
          let (newargs', newparams', oldargs) = unzip3 args'
          let newargs = concat newargs'
          let newparams = concat newparams'
          -- Create a new body that consists of a lambda for all new arguments and
          -- the old body applied to some arguments.
          let newbody = MkCore.mkCoreLams newparams (MkCore.mkCoreApps body oldargs)
          -- Create a new function with the same name but a new body
          newf <- Trans.lift $ mkFunction f newbody
          -- Replace the original application with one of the new function to the
          -- new arguments.
          change $ MkCore.mkCoreApps (Var newf) newargs
        False ->
          -- Don't change the expression if none of the arguments changed
          return expr
      
    -- If we don't have a body for the function called, leave it unchanged (it
    -- should be a primitive function then).
    Nothing -> return expr
  where
    -- Find the function called and the arguments
    (fexpr, args) = collectArgs expr
    Var f = fexpr

    -- Process a single argument and return (args, bndrs, arg), where args are
    -- the arguments to replace the given argument in the original
    -- application, bndrs are the binders to include in the top-level lambda
    -- in the new function body, and arg is the argument to apply to the old
    -- function body.
    doarg :: CoreExpr -> TransformMonad ([CoreExpr], [CoreBndr], CoreExpr)
    doarg arg = do
      repr <- isRepr arg
      bndrs <- Trans.lift getGlobalBinders
      let interesting var = Var.isLocalVar var && (not $ var `elem` bndrs)
      if not repr && not (is_var arg && interesting (exprToVar arg)) && not (has_free_tyvars arg) 
        then do
          -- Propagate all complex arguments that are not representable, but not
          -- arguments with free type variables (since those would require types
          -- not known yet, which will always be known eventually).
          -- Find interesting free variables, each of which should be passed to
          -- the new function instead of the original function argument.
          -- 
          -- Interesting vars are those that are local, but not available from the
          -- top level scope (functions from this module are defined as local, but
          -- they're not local to this function, so we can freely move references
          -- to them into another function).
          let free_vars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting arg
          -- Mark the current expression as changed
          setChanged
          return (map Var free_vars, free_vars, arg)
        else do
          -- Representable types will not be propagated, and arguments with free
          -- type variables will be propagated later.
          -- TODO: preserve original naming?
          id <- Trans.lift $ mkBinderFor arg "param"
          -- Just pass the original argument to the new function, which binds it
          -- to a new id and just pass that new id to the old function body.
          return ([arg], [id], mkReferenceTo id) 
-- Leave all other expressions unchanged
argprop expr = return expr
-- Perform this transform everywhere
argproptop = everywhere ("argprop", argprop)

--------------------------------
-- Function-typed argument extraction
--------------------------------
-- This transform takes any function-typed argument that cannot be propagated
-- (because the function that is applied to it is a builtin function), and
-- puts it in a brand new top level binder. This allows us to for example
-- apply map to a lambda expression This will not conflict with inlinenonrep,
-- since that only inlines local let bindings, not top level bindings.
funextract, funextracttop :: Transform
funextract expr@(App _ _) | is_var fexpr = do
  body_maybe <- Trans.lift $ getGlobalBind f
  case body_maybe of
    -- We don't have a function body for f, so we can perform this transform.
    Nothing -> do
      -- Find the new arguments
      args' <- mapM doarg args
      -- And update the arguments. We use return instead of changed, so the
      -- changed flag doesn't get set if none of the args got changed.
      return $ MkCore.mkCoreApps fexpr args'
    -- We have a function body for f, leave this application to funprop
    Just _ -> return expr
  where
    -- Find the function called and the arguments
    (fexpr, args) = collectArgs expr
    Var f = fexpr
    -- Change any arguments that have a function type, but are not simple yet
    -- (ie, a variable or application). This means to create a new function
    -- for map (\f -> ...) b, but not for map (foo a) b.
    --
    -- We could use is_applicable here instead of is_fun, but I think
    -- arguments to functions could only have forall typing when existential
    -- typing is enabled. Not sure, though.
    doarg arg | not (is_simple arg) && is_fun arg = do
      -- Create a new top level binding that binds the argument. Its body will
      -- be extended with lambda expressions, to take any free variables used
      -- by the argument expression.
      let free_vars = VarSet.varSetElems $ CoreFVs.exprFreeVars arg
      let body = MkCore.mkCoreLams free_vars arg
      id <- Trans.lift $ mkBinderFor body "fun"
      Trans.lift $ addGlobalBind id body
      -- Replace the argument with a reference to the new function, applied to
      -- all vars it uses.
      change $ MkCore.mkCoreApps (Var id) (map Var free_vars)
    -- Leave all other arguments untouched
    doarg arg = return arg

-- Leave all other expressions unchanged
funextract expr = return expr
-- Perform this transform everywhere
funextracttop = everywhere ("funextract", funextract)

--------------------------------
-- Ensure that a function that just returns another function (or rather,
-- another top-level binder) is still properly normalized. This is a temporary
-- solution, we should probably integrate this pass with lambdasimpl and
-- letsimpl instead.
--------------------------------
simplrestop expr@(Lam _ _) = return expr
simplrestop expr@(Let _ _) = return expr
simplrestop expr = do
  local_var <- Trans.lift $ is_local_var expr
  -- Don't extract values that are not representable, to prevent loops with
  -- inlinenonrep
  repr <- isRepr expr
  if local_var || not repr
    then
      return expr
    else do
      id <- Trans.lift $ mkBinderFor expr "res" 
      change $ Let (NonRec id expr) (Var id)
--------------------------------
-- End of transformations
--------------------------------




-- What transforms to run?
transforms = [inlinetopleveltop, argproptop, funextracttop, etatop, betatop, castproptop, letremovesimpletop, letderectop, letremovetop, letsimpltop, letflattop, scrutsimpltop, scrutbndrremovetop, casesimpltop, caseremovetop, inlinenonreptop, appsimpltop, letremoveunusedtop, castsimpltop, lambdasimpltop, simplrestop]

-- | Returns the normalized version of the given function.
getNormalized ::
  CoreBndr -- ^ The function to get
  -> TranslatorSession CoreExpr -- The normalized function body

getNormalized bndr = Utils.makeCached bndr tsNormalized $ do
  if is_poly (Var bndr)
    then
      -- This should really only happen at the top level... TODO: Give
      -- a different error if this happens down in the recursion.
      error $ "\nNormalize.normalizeBind: Function " ++ show bndr ++ " is polymorphic, can't normalize"
    else do
      expr <- getBinding bndr
      normalizeExpr (show bndr) expr

-- | Normalize an expression
normalizeExpr ::
  String -- ^ What are we normalizing? For debug output only.
  -> CoreSyn.CoreExpr -- ^ The expression to normalize 
  -> TranslatorSession CoreSyn.CoreExpr -- ^ The normalized expression

normalizeExpr what expr = do
      expr_uniqued <- genUniques expr
      -- Normalize this expression
      trace (what ++ " before normalization:\n\n" ++ showSDoc ( ppr expr_uniqued ) ++ "\n") $ return ()
      expr' <- dotransforms transforms expr_uniqued
      trace ("\n" ++ what ++ " after normalization:\n\n" ++ showSDoc ( ppr expr')) $ return ()
      return expr'

-- | Get the value that is bound to the given binder at top level. Fails when
--   there is no such binding.
getBinding ::
  CoreBndr -- ^ The binder to get the expression for
  -> TranslatorSession CoreExpr -- ^ The value bound to the binder

getBinding bndr = Utils.makeCached bndr tsBindings $ do
  -- If the binding isn't in the "cache" (bindings map), then we can't create
  -- it out of thin air, so return an error.
  error $ "Normalize.getBinding: Unknown function requested: " ++ show bndr

-- | Split a normalized expression into the argument binders, top level
--   bindings and the result binder.
splitNormalized ::
  CoreExpr -- ^ The normalized expression
  -> ([CoreBndr], [Binding], CoreBndr)
splitNormalized expr = (args, binds, res)
  where
    (args, letexpr) = CoreSyn.collectBinders expr
    (binds, resexpr) = flattenLets letexpr
    res = case resexpr of 
      (Var x) -> x
      _ -> error $ "Normalize.splitNormalized: Not in normal form: " ++ pprString expr ++ "\n"
