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
import qualified Control.Monad.Trans.Class as Trans
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Writer as Writer
import qualified Data.Accessor.Monad.Trans.State as MonadState
import qualified Data.Monoid as Monoid
import qualified Data.Map as Map

-- GHC API
import CoreSyn
import qualified CoreUtils
import qualified BasicTypes
import qualified Type
import qualified TysWiredIn
import qualified Id
import qualified Var
import qualified Name
import qualified DataCon
import qualified VarSet
import qualified CoreFVs
import qualified Class
import qualified MkCore
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import CLasH.Normalize.NormalizeTypes
import CLasH.Translator.TranslatorTypes
import CLasH.Normalize.NormalizeTools
import CLasH.VHDL.Constants (builtinIds)
import qualified CLasH.Utils as Utils
import CLasH.Utils.Core.CoreTools
import CLasH.Utils.Core.BinderTools
import CLasH.Utils.Pretty

----------------------------------------------------------------
-- Cleanup transformations
----------------------------------------------------------------

--------------------------------
-- β-reduction
--------------------------------
beta :: Transform
-- Substitute arg for x in expr. For value lambda's, also clone before
-- substitution.
beta c (App (Lam x expr) arg) | CoreSyn.isTyVar x = setChanged >> substitute x arg c expr
                              | otherwise         = setChanged >> substitute_clone x arg c expr
-- Leave all other expressions unchanged
beta c expr = return expr

--------------------------------
-- Unused let binding removal
--------------------------------
letremoveunused :: Transform
letremoveunused c expr@(Let (NonRec b bound) res) = do
  let used = expr_uses_binders [b] res
  if used
    then return expr
    else change res
letremoveunused c expr@(Let (Rec binds) res) = do
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
letremoveunused c expr = return expr

--------------------------------
-- empty let removal
--------------------------------
-- Remove empty (recursive) lets
letremove :: Transform
letremove c (Let (Rec []) res) = change res
-- Leave all other expressions unchanged
letremove c expr = return expr

--------------------------------
-- Simple let binding removal
--------------------------------
-- Remove a = b bindings from let expressions everywhere
letremovesimple :: Transform
letremovesimple = inlinebind (\(b, e) -> Trans.lift $ is_local_var e)

--------------------------------
-- Cast propagation
--------------------------------
-- Try to move casts as much downward as possible.
castprop :: Transform
castprop c (Cast (Let binds expr) ty) = change $ Let binds (Cast expr ty)
castprop c expr@(Cast (Case scrut b _ alts) ty) = change (Case scrut b ty alts')
  where
    alts' = map (\(con, bndrs, expr) -> (con, bndrs, (Cast expr ty))) alts
-- Leave all other expressions unchanged
castprop c expr = return expr

--------------------------------
-- Cast simplification. Mostly useful for state packing and unpacking, but
-- perhaps for others as well.
--------------------------------
castsimpl :: Transform
castsimpl c expr@(Cast val ty) = do
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
castsimpl c expr = return expr

--------------------------------
-- Top level function inlining
--------------------------------
-- This transformation inlines simple top level bindings. Simple
-- currently means that the body is only a single application (though
-- the complexity of the arguments is not currently checked) or that the
-- normalized form only contains a single binding. This should catch most of the
-- cases where a top level function is created that simply calls a type class
-- method with a type and dictionary argument, e.g.
--   fromInteger = GHC.Num.fromInteger (SizedWord D8) $dNum
-- which is later called using simply
--   fromInteger (smallInteger 10)
--
-- These useless wrappers are created by GHC automatically. If we don't
-- inline them, we get loads of useless components cluttering the
-- generated VHDL.
--
-- Note that the inlining could also inline simple functions defined by
-- the user, not just GHC generated functions. It turns out to be near
-- impossible to reliably determine what functions are generated and
-- what functions are user-defined. Instead of guessing (which will
-- inline less than we want) we will just inline all simple functions.
--
-- Only functions that are actually completely applied and bound by a
-- variable in a let expression are inlined. These are the expressions
-- that will eventually generate instantiations of trivial components.
-- By not inlining any other reference, we also prevent looping problems
-- with funextract and inlinedict.
inlinetoplevel :: Transform
inlinetoplevel (LetBinding:_) expr | not (is_fun expr) =
  case collectArgs expr of
	(Var f, args) -> do
	  body_maybe <- needsInline f
	  case body_maybe of
		Just body -> do
			-- Regenerate all uniques in the to-be-inlined expression
			body_uniqued <- Trans.lift $ genUniques body
			-- And replace the variable reference with the unique'd body.
			change (mkApps body_uniqued args)
			-- No need to inline
		Nothing -> return expr
	-- This is not an application of a binder, leave it unchanged.
	_ -> return expr

-- Leave all other expressions unchanged
inlinetoplevel c expr = return expr

-- | Does the given binder need to be inlined? If so, return the body to
-- be used for inlining.
needsInline :: CoreBndr -> TransformMonad (Maybe CoreExpr)
needsInline f = do
  body_maybe <- Trans.lift $ getGlobalBind f
  case body_maybe of
    -- No body available?
    Nothing -> return Nothing
    Just body -> case CoreSyn.collectArgs body of
      -- The body is some (top level) binder applied to 0 or more
      -- arguments. That should be simple enough to inline.
      (Var f, args) -> return $ Just body
      -- Body is more complicated, try normalizing it
      _ -> do
        norm_maybe <- Trans.lift $ getNormalized_maybe False f
        case norm_maybe of
          -- Noth normalizeable
          Nothing -> return Nothing 
          Just norm -> case splitNormalizedNonRep norm of
            -- The function has just a single binding, so that's simple
            -- enough to inline.
            (args, [bind], Var res) -> return $ Just norm
            -- More complicated function, don't inline
            _ -> return Nothing


----------------------------------------------------------------
-- Program structure transformations
----------------------------------------------------------------

--------------------------------
-- η expansion
--------------------------------
-- Make sure all parameters to the normalized functions are named by top
-- level lambda expressions. For this we apply η expansion to the
-- function body (possibly enclosed in some lambda abstractions) while
-- it has a function type. Eventually this will result in a function
-- body consisting of a bunch of nested lambdas containing a
-- non-function value (e.g., a complete application).
eta :: Transform
eta (AppFirst:_) expr = return expr
-- Also don't apply to arguments, since this can cause loops with
-- funextract. This isn't the proper solution, but due to an
-- implementation bug in notappargs, this is how it used to work so far.
eta (AppSecond:_) expr = return expr
eta c expr | is_fun expr && not (is_lam expr) = do
 let arg_ty = (fst . Type.splitFunTy . CoreUtils.exprType) expr
 id <- Trans.lift $ mkInternalVar "param" arg_ty
 change (Lam id (App expr (Var id)))
-- Leave all other expressions unchanged
eta c e = return e

--------------------------------
-- Application propagation
--------------------------------
-- Move applications into let and case expressions.
appprop :: Transform
-- Propagate the application into the let
appprop c (App (Let binds expr) arg) = change $ Let binds (App expr arg)
-- Propagate the application into each of the alternatives
appprop c (App (Case scrut b ty alts) arg) = change $ Case scrut b ty' alts'
  where 
    alts' = map (\(con, bndrs, expr) -> (con, bndrs, (App expr arg))) alts
    ty' = CoreUtils.applyTypeToArg ty arg
-- Leave all other expressions unchanged
appprop c expr = return expr

--------------------------------
-- Let recursification
--------------------------------
-- Make all lets recursive, so other transformations don't need to
-- handle non-recursive lets
letrec :: Transform
letrec c expr@(Let (NonRec bndr val) res) = 
  change $ Let (Rec [(bndr, val)]) res

-- Leave all other expressions unchanged
letrec c expr = return expr

--------------------------------
-- let flattening
--------------------------------
-- Takes a let that binds another let, and turns that into two nested lets.
-- e.g., from:
-- let b = (let b' = expr' in res') in res
-- to:
-- let b' = expr' in (let b = res' in res)
letflat :: Transform
-- Turn a nonrec let that binds a let into two nested lets.
letflat c (Let (NonRec b (Let binds  res')) res) = 
  change $ Let binds (Let (NonRec b res') res)
letflat c (Let (Rec binds) expr) = do
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
letflat c expr = return expr

--------------------------------
-- Return value simplification
--------------------------------
-- Ensure the return value of a function follows proper normal form. eta
-- expansion ensures the body starts with lambda abstractions, this
-- transformation ensures that the lambda abstractions always contain a
-- recursive let and that, when the return value is representable, the
-- let contains a local variable reference in its body.

-- Extract the return value from the body of the top level lambdas (of
-- which ther could be zero), unless it is a let expression (in which
-- case the next clause applies).
retvalsimpl c expr | all (== LambdaBody) c && not (is_lam expr) && not (is_let expr) = do
  local_var <- Trans.lift $ is_local_var expr
  repr <- isRepr expr
  if not local_var && repr
    then do
      id <- Trans.lift $ mkBinderFor expr "res" 
      change $ Let (Rec [(id, expr)]) (Var id)
    else
      return expr
-- Extract the return value from the body of a let expression, which is
-- itself the body of the top level lambdas (of which there could be
-- zero).
retvalsimpl c expr@(Let (Rec binds) body) | all (== LambdaBody) c = do
  -- Don't extract values that are already a local variable, to prevent
  -- loops with ourselves.
  local_var <- Trans.lift $ is_local_var body
  -- Don't extract values that are not representable, to prevent loops with
  -- inlinenonrep
  repr <- isRepr body
  if not local_var && repr
    then do
      id <- Trans.lift $ mkBinderFor body "res" 
      change $ Let (Rec ((id, body):binds)) (Var id)
    else
      return expr
-- Leave all other expressions unchanged
retvalsimpl c expr = return expr

--------------------------------
-- Representable arguments simplification
--------------------------------
-- Make sure that all arguments of a representable type are simple variables.
appsimpl :: Transform
-- Simplify all representable arguments. Do this by introducing a new Let
-- that binds the argument and passing the new binder in the application.
appsimpl c expr@(App f arg) = do
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
appsimpl c expr = return expr

----------------------------------------------------------------
-- Built-in function transformations
----------------------------------------------------------------

--------------------------------
-- Function-typed argument extraction
--------------------------------
-- This transform takes any function-typed argument that cannot be propagated
-- (because the function that is applied to it is a builtin function), and
-- puts it in a brand new top level binder. This allows us to for example
-- apply map to a lambda expression This will not conflict with inlinenonrep,
-- since that only inlines local let bindings, not top level bindings.
funextract :: Transform
funextract c expr@(App _ _) | is_var fexpr = do
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
    doarg arg | not (is_simple arg) && is_fun arg && not (has_free_tyvars arg) = do
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
funextract c expr = return expr




----------------------------------------------------------------
-- Case normalization transformations
----------------------------------------------------------------

--------------------------------
-- Scrutinee simplification
--------------------------------
-- Make sure the scrutinee of a case expression is a local variable
-- reference.
scrutsimpl :: Transform
-- Replace a case expression with a let that binds the scrutinee and a new
-- simple scrutinee, but only when the scrutinee is representable (to prevent
-- loops with inlinenonrep, though I don't think a non-representable scrutinee
-- will be supported anyway...) and is not a local variable already.
scrutsimpl c expr@(Case scrut b ty alts) = do
  repr <- isRepr scrut
  local_var <- Trans.lift $ is_local_var scrut
  if repr && not local_var
    then do
      id <- Trans.lift $ mkBinderFor scrut "scrut"
      change $ Let (NonRec id scrut) (Case (Var id) b ty alts)
    else
      return expr
-- Leave all other expressions unchanged
scrutsimpl c expr = return expr

--------------------------------
-- Scrutinee binder removal
--------------------------------
-- A case expression can have an extra binder, to which the scrutinee is bound
-- after bringing it to WHNF. This is used for forcing evaluation of strict
-- arguments. Since strictness does not matter for us (rather, everything is
-- sort of strict), this binder is ignored when generating VHDL, and must thus
-- be wild in the normal form.
scrutbndrremove :: Transform
-- If the scrutinee is already simple, and the bndr is not wild yet, replace
-- all occurences of the binder with the scrutinee variable.
scrutbndrremove c (Case (Var scrut) bndr ty alts) | bndr_used = do
    alts' <- mapM subs_bndr alts
    change $ Case (Var scrut) wild ty alts'
  where
    is_used (_, _, expr) = expr_uses_binders [bndr] expr
    bndr_used = or $ map is_used alts
    subs_bndr (con, bndrs, expr) = do
      expr' <- substitute bndr (Var scrut) c expr
      return (con, bndrs, expr')
    wild = MkCore.mkWildBinder (Id.idType bndr)
-- Leave all other expressions unchanged
scrutbndrremove c expr = return expr

--------------------------------
-- Case normalization
--------------------------------
-- Turn a case expression with any number of alternatives with any
-- number of non-wild binders into as set of case and let expressions,
-- all of which are in normal form (e.g., a bunch of extractor case
-- expressions to extract all fields from the scrutinee, a number of let
-- bindings to bind each alternative and a single selector case to
-- select the right value.
casesimpl :: Transform
-- This is already a selector case (or, if x does not appear in bndrs, a very
-- simple case statement that will be removed by caseremove below). Just leave
-- it be.
casesimpl c expr@(Case scrut b ty [(con, bndrs, Var x)]) = return expr
-- Make sure that all case alternatives have only wild binders and simple
-- expressions.
-- This is done by creating a new let binding for each non-wild binder, which
-- is bound to a new simple selector case statement and for each complex
-- expression. We do this only for representable types, to prevent loops with
-- inlinenonrep.
casesimpl c expr@(Case scrut bndr ty alts) | not bndr_used = do
  (bindingss, alts') <- (Monad.liftM unzip) $ mapM doalt alts
  let bindings = concat bindingss
  -- Replace the case with a let with bindings and a case
  let newlet = mkNonRecLets bindings (Case scrut bndr ty alts')
  -- If there are no non-wild binders, or this case is already a simple
  -- selector (i.e., a single alt with exactly one binding), already a simple
  -- selector altan no bindings (i.e., no wild binders in the original case),
  -- don't change anything, otherwise, replace the case.
  if null bindings then return expr else change newlet 
  where
  -- Check if the scrutinee binder is used
  is_used (_, _, expr) = expr_uses_binders [bndr] expr
  bndr_used = or $ map is_used alts
  -- Generate a single wild binder, since they are all the same
  wild = MkCore.mkWildBinder
  -- Wilden the binders of one alt, producing a list of bindings as a
  -- sideeffect.
  doalt :: CoreAlt -> TransformMonad ([(CoreBndr, CoreExpr)], CoreAlt)
  doalt (LitAlt _, _, _) = error $ "Don't know how to handle LitAlt in case expression: " ++ pprString expr
  doalt alt@(DEFAULT, [], expr) = return ([], alt)
  doalt (DataAlt dc, bndrs, expr) = do
    -- Make each binder wild, if possible
    bndrs_res <- Monad.zipWithM dobndr bndrs [0..]
    let (newbndrs, bindings_maybe) = unzip bndrs_res
    -- Extract a complex expression, if possible. For this we check if any of
    -- the new list of bndrs are used by expr. We can't use free_vars here,
    -- since that looks at the old bndrs.
    let uses_bndrs = not $ VarSet.isEmptyVarSet $ CoreFVs.exprSomeFreeVars (`elem` newbndrs) expr
    (exprbinding_maybe, expr') <- doexpr expr uses_bndrs
    -- Create a new alternative
    let newalt = (DataAlt dc, newbndrs, expr')
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
            let dc_i = datacon_index (CoreUtils.exprType scrut) dc
            caseexpr <- Trans.lift $ mkSelCase scrut dc_i i
            -- Create a new binder that will actually capture a value in this
            -- case statement, and return it.
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
            return (Just (id, expr), Var id)
          else
            -- Don't simplify anything else
            return (Nothing, expr)
-- Leave all other expressions unchanged
casesimpl c expr = return expr

--------------------------------
-- Case removal
--------------------------------
-- Remove case statements that have only a single alternative and only wild
-- binders.
caseremove :: Transform
-- Replace a useless case by the value of its single alternative
caseremove c (Case scrut b ty [(con, bndrs, expr)]) | not usesvars = change expr
    -- Find if any of the binders are used by expr
    where usesvars = (not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` b:bndrs))) expr
-- Leave all other expressions unchanged
caseremove c expr = return expr

--------------------------------
-- Case of known constructor simplification
--------------------------------
-- If a case expressions scrutinizes a datacon application, we can
-- determine which alternative to use and remove the case alltogether.
-- We replace it with a let expression the binds every binder in the
-- alternative bound to the corresponding argument of the datacon. We do
-- this instead of substituting the binders, to prevent duplication of
-- work and preserve sharing wherever appropriate.
knowncase :: Transform
knowncase context expr@(Case scrut@(App _ _) bndr ty alts) | not bndr_used = do
    case collectArgs scrut of
      (Var f, args) -> case Id.isDataConId_maybe f of
        -- Not a dataconstructor? Don't change anything (probably a
        -- function, then)
        Nothing -> return expr
        Just dc -> do
          let (altcon, bndrs, res) =  case List.find (\(altcon, bndrs, res) -> altcon == (DataAlt dc)) alts of
                Just alt -> alt -- Return the alternative found
                Nothing -> head alts -- If the datacon is not present, the first must be the default alternative
          -- Double check if we have either the correct alternative, or
          -- the default.
          if altcon /= (DataAlt dc) && altcon /= DEFAULT then error ("Normalize.knowncase: Invalid core, datacon not found in alternatives and DEFAULT alternative is not first? " ++ pprString expr) else return ()
          -- Find out how many arguments to drop (type variables and
          -- predicates like dictionaries).
          let (tvs, preds, _, _) = DataCon.dataConSig dc
          let count = length tvs + length preds
          -- Create a let expression that binds each of the binders in
          -- this alternative to the corresponding argument of the data
          -- constructor.
          let binds = zip bndrs (drop count args)
          change $ Let (Rec binds) res
      _ -> return expr -- Scrutinee is not an application of a var
  where
    is_used (_, _, expr) = expr_uses_binders [bndr] expr
    bndr_used = or $ map is_used alts

-- Leave all other expressions unchanged
knowncase c expr = return expr




----------------------------------------------------------------
-- Unrepresentable value removal transformations
----------------------------------------------------------------

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
inlinenonrep :: Transform
inlinenonrep = inlinebind ((Monad.liftM not) . isRepr . snd)

--------------------------------
-- Function specialization
--------------------------------
-- Remove all applications to non-representable arguments, by duplicating the
-- function called with the non-representable parameter replaced by the free
-- variables of the argument passed in.
argprop :: Transform
-- Transform any application of a named function (i.e., skip applications of
-- lambda's). Also skip applications that have arguments with free type
-- variables, since we can't inline those.
argprop c expr@(App _ _) | is_var fexpr = do
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

          Trans.lift $ MonadState.modify tsInitStates (\ismap ->
            let init_state_maybe = Map.lookup f ismap in
            case init_state_maybe of
              Nothing -> ismap
              Just init_state -> Map.insert newf init_state ismap)
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
      let interesting var = Var.isLocalVar var && (var `notElem` bndrs)
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
          -- TODO: Clone the free_vars (and update references in arg), since
          -- this might cause conflicts if two arguments that are propagated
          -- share a free variable. Also, we are now introducing new variables
          -- into a function that are not fresh, which violates the binder
          -- uniqueness invariant.
          return (map Var free_vars, free_vars, arg)
        else do
          -- Representable types will not be propagated, and arguments with free
          -- type variables will be propagated later.
          -- Note that we implicitly remove any type variables in the type of
          -- the original argument by using the type of the actual argument
          -- for the new formal parameter.
          -- TODO: preserve original naming?
          id <- Trans.lift $ mkBinderFor arg "param"
          -- Just pass the original argument to the new function, which binds it
          -- to a new id and just pass that new id to the old function body.
          return ([arg], [id], mkReferenceTo id) 
-- Leave all other expressions unchanged
argprop c expr = return expr

--------------------------------
-- Non-representable result inlining
--------------------------------
-- This transformation takes a function (top level binding) that has a
-- non-representable result (e.g., a tuple containing a function, or an
-- Integer. The latter can occur in some cases as the result of the
-- fromIntegerT function) and inlines enough of the function to make the
-- result representable again.
--
-- This is done by first normalizing the function and then "inlining"
-- the result. Since no unrepresentable let bindings are allowed in
-- normal form, we can be sure that all free variables of the result
-- expression will be representable (Note that we probably can't
-- guarantee that all representable parts of the expression will be free
-- variables, so we might inline more than strictly needed).
--
-- The new function result will be a tuple containing all free variables
-- of the old result, so the old result can be rebuild at the caller.
--
-- We take care not to inline dictionary id's, which are top level
-- bindings with a non-representable result type as well, since those
-- will never become VHDL signals directly. There is a separate
-- transformation (inlinedict) that specifically inlines dictionaries
-- only when it is useful.
inlinenonrepresult :: Transform

-- Apply to any (application of) a reference to a top level function
-- that is fully applied (i.e., dos not have a function type) but is not
-- representable. We apply in any context, since non-representable
-- expressions are generally left alone and can occur anywhere.
inlinenonrepresult context expr | not (is_applicable expr) && not (has_free_tyvars expr) =
  case collectArgs expr of
    (Var f, args) | not (Id.isDictId f) -> do
      repr <- isRepr expr
      if not repr
        then do
          body_maybe <- Trans.lift $ getNormalized_maybe True f
          case body_maybe of
            Just body -> do
              let (bndrs, binds, res) = splitNormalizedNonRep body
              if has_free_tyvars res 
                then
                  -- Don't touch anything with free type variables, since
                  -- we can't return those. We'll wait until argprop
                  -- removed those variables.
                  return expr
                else do
                  -- Get the free local variables of res
                  global_bndrs <- Trans.lift getGlobalBinders
                  let interesting var = Var.isLocalVar var && (var `notElem` global_bndrs)
                  let free_vars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting res
                  let free_var_types = map Id.idType free_vars
                  let n_free_vars = length free_vars
                  -- Get a tuple datacon to wrap around the free variables
                  let fvs_datacon = TysWiredIn.tupleCon BasicTypes.Boxed n_free_vars
                  let fvs_datacon_id = DataCon.dataConWorkId fvs_datacon
                  -- Let the function now return a tuple with references to
                  -- all free variables of the old return value. First pass
                  -- all the types of the variables, since tuple
                  -- constructors are polymorphic.
                  let newres = mkApps (Var fvs_datacon_id) (map Type free_var_types ++  map Var free_vars)
                  -- Recreate the function body with the changed return value
                  let newbody = mkLams bndrs (Let (Rec binds) newres) 
                  -- Create the new function
                  f' <- Trans.lift $ mkFunction f newbody

                  -- Call the new function
                  let newapp = mkApps (Var f') args
                  res_bndr <- Trans.lift $ mkBinderFor newapp "res"
                  -- Create extractor case expressions to extract each of the
                  -- free variables from the tuple.
                  sel_cases <- Trans.lift $ mapM (mkSelCase (Var res_bndr) 0) [0..n_free_vars-1]

                  -- Bind the res_bndr to the result of the new application
                  -- and each of the free variables to the corresponding
                  -- selector case. Replace the let body with the original
                  -- body of the called function (which can still access all
                  -- of its free variables, from the let).
                  let binds = (res_bndr, newapp):(zip free_vars sel_cases)
                  let letexpr = Let (Rec binds) res

                  -- Finally, regenarate all uniques in the new expression,
                  -- since the free variables could otherwise become
                  -- duplicated. It is not strictly necessary to regenerate
                  -- res, since we're moving that expression, but it won't
                  -- hurt.
                  letexpr_uniqued <- Trans.lift $ genUniques letexpr
                  change letexpr_uniqued
            Nothing -> return expr
        else
          -- Don't touch representable expressions or (applications of)
          -- dictionary ids.
          return expr
    -- Not a reference to or application of a top level function
    _ -> return expr
-- Leave all other expressions unchanged
inlinenonrepresult c expr = return expr

----------------------------------------------------------------
-- Type-class transformations
----------------------------------------------------------------

--------------------------------
-- ClassOp resolution
--------------------------------
-- Resolves any class operation to the actual operation whenever
-- possible. Class methods (as well as parent dictionary selectors) are
-- special "functions" that take a type and a dictionary and evaluate to
-- the corresponding method. A dictionary is nothing more than a
-- special dataconstructor applied to the type the dictionary is for,
-- each of the superclasses and all of the class method definitions for
-- that particular type. Since dictionaries all always inlined (top
-- levels dictionaries are inlined by inlinedict, local dictionaries are
-- inlined by inlinenonrep), we will eventually have something like:
--
--   baz
--     @ CLasH.HardwareTypes.Bit
--     (D:Baz @ CLasH.HardwareTypes.Bit bitbaz)
--
-- Here, baz is the method selector for the baz method, while
-- D:Baz is the dictionary constructor for the Baz and bitbaz is the baz
-- method defined in the Baz Bit instance declaration.
--
-- To resolve this, we can look at the ClassOp IdInfo from the baz Id,
-- which contains the Class it is defined for. From the Class, we can
-- get a list of all selectors (both parent class selectors as well as
-- method selectors). Since the arguments to D:Baz (after the type
-- argument) correspond exactly to this list, we then look up baz in
-- that list and replace the entire expression by the corresponding 
-- argument to D:Baz.
--
-- We don't resolve methods that have a builtin translation (such as
-- ==), since the actual implementation is not always (easily)
-- translateable. For example, when deriving ==, GHC generates code
-- using $con2tag functions to translate a datacon to an int and compare
-- that with GHC.Prim.==# . Better to avoid that for now.
classopresolution :: Transform
classopresolution c expr@(App (App (Var sel) ty) dict) | not is_builtin =
  case Id.isClassOpId_maybe sel of
    -- Not a class op selector
    Nothing -> return expr
    Just cls -> case collectArgs dict of
      (_, []) -> return expr -- Dict is not an application (e.g., not inlined yet)
      (Var dictdc, (ty':selectors)) | not (Maybe.isJust (Id.isDataConId_maybe dictdc)) -> return expr -- Dictionary is not a datacon yet (but e.g., a top level binder)
                                | tyargs_neq ty ty' -> error $ "Normalize.classopresolution: Applying class selector to dictionary without matching type?\n" ++ pprString expr
                                | otherwise ->
        let selector_ids = Class.classSelIds cls in
        -- Find the selector used in the class' list of selectors
        case List.elemIndex sel selector_ids of
          Nothing -> error $ "Normalize.classopresolution: Selector not found in class' selector list? This should not happen!\nExpression: " ++ pprString expr ++ "\nClass: " ++ show cls ++ "\nSelectors: " ++ show selector_ids
          -- Get the corresponding argument from the dictionary
          Just n -> change (selectors!!n)
      (_, _) -> return expr -- Not applying a variable? Don't touch
  where
    -- Compare two type arguments, returning True if they are _not_
    -- equal
    tyargs_neq (Type ty1) (Type ty2) = not $ Type.coreEqType ty1 ty2
    tyargs_neq _ _ = True
    -- Is this a builtin function / method?
    is_builtin = elem (Name.getOccString sel) builtinIds

-- Leave all other expressions unchanged
classopresolution c expr = return expr

--------------------------------
-- Dictionary inlining
--------------------------------
-- Inline all top level dictionaries, that are in a position where
-- classopresolution can actually resolve them. This makes this
-- transformation look similar to classoperesolution below, but we'll
-- keep them separated for clarity. By not inlining other dictionaries,
-- we prevent expression sizes exploding when huge type level integer
-- dictionaries are inlined which can never be expanded (in casts, for
-- example).
inlinedict c expr@(App (App (Var sel) ty) (Var dict)) | not is_builtin && is_classop = do
  body_maybe <- Trans.lift $ getGlobalBind dict
  case body_maybe of
    -- No body available (no source available, or a local variable /
    -- argument)
    Nothing -> return expr
    Just body -> change (App (App (Var sel) ty) body)
  where
    -- Is this a builtin function / method?
    is_builtin = elem (Name.getOccString sel) builtinIds
    -- Are we dealing with a class operation selector?
    is_classop = Maybe.isJust (Id.isClassOpId_maybe sel)

-- Leave all other expressions unchanged
inlinedict c expr = return expr


{-
--------------------------------
-- Identical let binding merging
--------------------------------
-- Merge two bindings in a let if they are identical 
-- TODO: We would very much like to use GHC's CSE module for this, but that
-- doesn't track if something changed or not, so we can't use it properly.
letmerge :: Transform
letmerge c expr@(Let _ _) = do
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
letmerge c expr = return expr
-}

--------------------------------
-- End of transformations
--------------------------------




-- What transforms to run?
transforms = [ ("inlinedict", inlinedict)
             , ("inlinetoplevel", inlinetoplevel)
             , ("inlinenonrepresult", inlinenonrepresult)
             , ("knowncase", knowncase)
             , ("classopresolution", classopresolution)
             , ("argprop", argprop)
             , ("funextract", funextract)
             , ("eta", eta)
             , ("beta", beta)
             , ("appprop", appprop)
             , ("castprop", castprop)
             , ("letremovesimple", letremovesimple)
             , ("letrec", letrec)
             , ("letremove", letremove)
             , ("retvalsimpl", retvalsimpl)
             , ("letflat", letflat)
             , ("scrutsimpl", scrutsimpl)
             , ("scrutbndrremove", scrutbndrremove)
             , ("casesimpl", casesimpl)
             , ("caseremove", caseremove)
             , ("inlinenonrep", inlinenonrep)
             , ("appsimpl", appsimpl)
             , ("letremoveunused", letremoveunused)
             , ("castsimpl", castsimpl)
             ]

-- | Returns the normalized version of the given function, or an error
-- if it is not a known global binder.
getNormalized ::
  Bool -- ^ Allow the result to be unrepresentable?
  -> CoreBndr -- ^ The function to get
  -> TranslatorSession CoreExpr -- The normalized function body
getNormalized result_nonrep bndr = do
  norm <- getNormalized_maybe result_nonrep bndr
  return $ Maybe.fromMaybe
    (error $ "Normalize.getNormalized: Unknown or non-representable function requested: " ++ show bndr)
    norm

-- | Returns the normalized version of the given function, or Nothing
-- when the binder is not a known global binder or is not normalizeable.
getNormalized_maybe ::
  Bool -- ^ Allow the result to be unrepresentable?
  -> CoreBndr -- ^ The function to get
  -> TranslatorSession (Maybe CoreExpr) -- The normalized function body

getNormalized_maybe result_nonrep bndr = do
    expr_maybe <- getGlobalBind bndr
    normalizeable <- isNormalizeable result_nonrep bndr
    if not normalizeable || Maybe.isNothing expr_maybe
      then
        -- Binder not normalizeable or not found
        return Nothing
      else do
        -- Binder found and is monomorphic. Normalize the expression
        -- and cache the result.
        normalized <- Utils.makeCached bndr tsNormalized $ 
          normalizeExpr (show bndr) (Maybe.fromJust expr_maybe)
        return (Just normalized)

-- | Normalize an expression
normalizeExpr ::
  String -- ^ What are we normalizing? For debug output only.
  -> CoreSyn.CoreExpr -- ^ The expression to normalize 
  -> TranslatorSession CoreSyn.CoreExpr -- ^ The normalized expression

normalizeExpr what expr = do
      startcount <- MonadState.get tsTransformCounter 
      expr_uniqued <- genUniques expr
      -- Do a debug print, if requested
      let expr_uniqued' = Utils.traceIf (normalize_debug >= NormDbgFinal) (what ++ " before normalization:\n\n" ++ showSDoc ( ppr expr_uniqued ) ++ "\n") expr_uniqued
      -- Normalize this expression
      expr' <- dotransforms transforms expr_uniqued'
      endcount <- MonadState.get tsTransformCounter 
      -- Do a debug print, if requested
      Utils.traceIf (normalize_debug >= NormDbgFinal)  (what ++ " after normalization:\n\n" ++ showSDoc ( ppr expr') ++ "\nNeeded " ++ show (endcount - startcount) ++ " transformations to normalize " ++ what) $
        return expr'

-- | Split a normalized expression into the argument binders, top level
--   bindings and the result binder. This function returns an error if
--   the type of the expression is not representable.
splitNormalized ::
  CoreExpr -- ^ The normalized expression
  -> ([CoreBndr], [Binding], CoreBndr)
splitNormalized expr = 
  case splitNormalizedNonRep expr of
    (args, binds, Var res) -> (args, binds, res)
    _ -> error $ "Normalize.splitNormalized: Not in normal form: " ++ pprString expr ++ "\n"

-- Split a normalized expression, whose type can be unrepresentable.
splitNormalizedNonRep::
  CoreExpr -- ^ The normalized expression
  -> ([CoreBndr], [Binding], CoreExpr)
splitNormalizedNonRep expr = (args, binds, resexpr)
  where
    (args, letexpr) = CoreSyn.collectBinders expr
    (binds, resexpr) = flattenLets letexpr
