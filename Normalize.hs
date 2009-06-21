{-# LANGUAGE PackageImports #-}
--
-- Functions to bring a Core expression in normal form. This module provides a
-- top level function "normalize", and defines the actual transformation passes that
-- are performed.
--
module Normalize (normalizeModule) where

-- Standard modules
import Debug.Trace
import qualified Maybe
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
import qualified Id
import qualified Var
import qualified VarSet
import qualified CoreFVs
import qualified CoreUtils
import qualified MkCore
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import NormalizeTypes
import NormalizeTools
import CoreTools

--------------------------------
-- Start of transformations
--------------------------------

--------------------------------
-- η abstraction
--------------------------------
eta, etatop :: Transform
eta expr | is_fun expr && not (is_lam expr) = do
  let arg_ty = (fst . Type.splitFunTy . CoreUtils.exprType) expr
  id <- mkInternalVar "param" arg_ty
  change (Lam id (App expr (Var id)))
-- Leave all other expressions unchanged
eta e = return e
etatop = notapplied ("eta", eta)

--------------------------------
-- β-reduction
--------------------------------
beta, betatop :: Transform
-- Substitute arg for x in expr
beta (App (Lam x expr) arg) = change $ substitute [(x, arg)] expr
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
-- let recursification
--------------------------------
letrec, letrectop :: Transform
letrec (Let (NonRec b expr) res) = change $ Let (Rec [(b, expr)]) res
-- Leave all other expressions unchanged
letrec expr = return expr
-- Perform this transform everywhere
letrectop = everywhere ("letrec", letrec)

--------------------------------
-- let simplification
--------------------------------
letsimpl, letsimpltop :: Transform
-- Don't simplifiy lets that are already simple
letsimpl expr@(Let _ (Var _)) = return expr
-- Put the "in ..." value of a let in its own binding, but not when the
-- expression is applicable (to prevent loops with inlinefun).
letsimpl (Let (Rec binds) expr) | not $ is_applicable expr = do
  id <- mkInternalVar "foo" (CoreUtils.exprType expr)
  let bind = (id, expr)
  change $ Let (Rec (bind:binds)) (Var id)
-- Leave all other expressions unchanged
letsimpl expr = return expr
-- Perform this transform everywhere
letsimpltop = everywhere ("letsimpl", letsimpl)

--------------------------------
-- let flattening
--------------------------------
letflat, letflattop :: Transform
letflat (Let (Rec binds) expr) = do
  -- Turn each binding into a list of bindings (possibly containing just one
  -- element, of course)
  bindss <- Monad.mapM flatbind binds
  -- Concat all the bindings
  let binds' = concat bindss
  -- Return the new let. We don't use change here, since possibly nothing has
  -- changed. If anything has changed, flatbind has already flagged that
  -- change.
  return $ Let (Rec binds') expr
  where
    -- Turns a binding of a let into a multiple bindings, or any other binding
    -- into a list with just that binding
    flatbind :: (CoreBndr, CoreExpr) -> TransformMonad [(CoreBndr, CoreExpr)]
    flatbind (b, Let (Rec binds) expr) = change ((b, expr):binds)
    flatbind (b, expr) = return [(b, expr)]
-- Leave all other expressions unchanged
letflat expr = return expr
-- Perform this transform everywhere
letflattop = everywhere ("letflat", letflat)

--------------------------------
-- Simple let binding removal
--------------------------------
-- Remove a = b bindings from let expressions everywhere
letremovetop :: Transform
letremovetop = everywhere ("letremove", inlinebind (\(b, e) -> case e of (Var v) -> True; otherwise -> False))

--------------------------------
-- Function inlining
--------------------------------
-- Remove a = B bindings, with B :: a -> b, or B :: forall x . T, from let
-- expressions everywhere. This means that any value that still needs to be
-- applied to something else (polymorphic values need to be applied to a
-- Type) will be inlined, and will eventually be applied to all their
-- arguments.
--
-- This is a tricky function, which is prone to create loops in the
-- transformations. To fix this, we make sure that no transformation will
-- create a new let binding with a function type. These other transformations
-- will just not work on those function-typed values at first, but the other
-- transformations (in particular β-reduction) should make sure that the type
-- of those values eventually becomes primitive.
inlinefuntop :: Transform
inlinefuntop = everywhere ("inlinefun", inlinebind (is_applicable . snd))

--------------------------------
-- Scrutinee simplification
--------------------------------
scrutsimpl,scrutsimpltop :: Transform
-- Don't touch scrutinees that are already simple
scrutsimpl expr@(Case (Var _) _ _ _) = return expr
-- Replace all other cases with a let that binds the scrutinee and a new
-- simple scrutinee, but not when the scrutinee is applicable (to prevent
-- loops with inlinefun, though I don't think a scrutinee can be
-- applicable...)
scrutsimpl (Case scrut b ty alts) | not $ is_applicable scrut = do
  id <- mkInternalVar "scrut" (CoreUtils.exprType scrut)
  change $ Let (Rec [(id, scrut)]) (Case (Var id) b ty alts)
-- Leave all other expressions unchanged
scrutsimpl expr = return expr
-- Perform this transform everywhere
scrutsimpltop = everywhere ("scrutsimpl", scrutsimpl)

--------------------------------
-- Case binder wildening
--------------------------------
casewild, casewildtop :: Transform
casewild expr@(Case scrut b ty alts) = do
  (bindingss, alts') <- (Monad.liftM unzip) $ mapM doalt alts
  let bindings = concat bindingss
  -- Replace the case with a let with bindings and a case
  let newlet = (Let (Rec bindings) (Case scrut b ty alts'))
  -- If there are no non-wild binders, or this case is already a simple
  -- selector (i.e., a single alt with exactly one binding), already a simple
  -- selector altan no bindings (i.e., no wild binders in the original case),
  -- don't change anything, otherwise, replace the case.
  if null bindings || length alts == 1 && length bindings == 1 then return expr else change newlet 
  where
  -- Generate a single wild binder, since they are all the same
  wild = Id.mkWildId
  -- Wilden the binders of one alt, producing a list of bindings as a
  -- sideeffect.
  doalt :: CoreAlt -> TransformMonad ([(CoreBndr, CoreExpr)], CoreAlt)
  doalt (con, bndrs, expr) = do
    bindings_maybe <- Monad.zipWithM mkextracts bndrs [0..]
    let bindings = Maybe.catMaybes bindings_maybe
    -- We replace the binders with wild binders only. We can leave expr
    -- unchanged, since the new bindings bind the same vars as the original
    -- did.
    let newalt = (con, wildbndrs, expr)
    return (bindings, newalt)
    where
      -- Make all binders wild
      wildbndrs = map (\bndr -> Id.mkWildId (Id.idType bndr)) bndrs
      -- Creates a case statement to retrieve the ith element from the scrutinee
      -- and binds that to b.
      mkextracts :: CoreBndr -> Int -> TransformMonad (Maybe (CoreBndr, CoreExpr))
      mkextracts b i =
        if is_wild b || Type.isFunTy (Id.idType b) 
          -- Don't create extra bindings for binders that are already wild, or
          -- for binders that bind function types (to prevent loops with
          -- inlinefun).
          then return Nothing
          else do
            -- Create on new binder that will actually capture a value in this
            -- case statement, and return it
            let bty = (Id.idType b)
            id <- mkInternalVar "sel" bty
            let binders = take i wildbndrs ++ [id] ++ drop (i+1) wildbndrs
            return $ Just (b, Case scrut b bty [(con, binders, Var id)])
-- Leave all other expressions unchanged
casewild expr = return expr
-- Perform this transform everywhere
casewildtop = everywhere ("casewild", casewild)

--------------------------------
-- Case value simplification
--------------------------------
casevalsimpl, casevalsimpltop :: Transform
casevalsimpl expr@(Case scrut b ty alts) = do
  -- Try to simplify each alternative, resulting in an optional binding and a
  -- new alternative.
  (bindings_maybe, alts') <- (Monad.liftM unzip) $ mapM doalt alts
  let bindings = Maybe.catMaybes bindings_maybe
  -- Create a new let around the case, that binds of the cases values.
  let newlet = Let (Rec bindings) (Case scrut b ty alts')
  -- If there were no values that needed and allowed simplification, don't
  -- change the case.
  if null bindings then return expr else change newlet 
  where
    doalt :: CoreAlt -> TransformMonad (Maybe (CoreBndr, CoreExpr), CoreAlt)
    -- Don't simplify values that are already simple
    doalt alt@(con, bndrs, Var _) = return (Nothing, alt)
    -- Simplify each alt by creating a new id, binding the case value to it and
    -- replacing the case value with that id. Only do this when the case value
    -- does not use any of the binders bound by this alternative, for that would
    -- cause those binders to become unbound when moving the value outside of
    -- the case statement. Also, don't create a binding for applicable
    -- expressions, to prevent loops with inlinefun.
    doalt (con, bndrs, expr) | (not usesvars) && (not $ is_applicable expr) = do
      id <- mkInternalVar "caseval" (CoreUtils.exprType expr)
      -- We don't flag a change here, since casevalsimpl will do that above
      -- based on Just we return here.
      return $ (Just (id, expr), (con, bndrs, Var id))
      -- Find if any of the binders are used by expr
      where usesvars = (not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` bndrs))) expr
    -- Don't simplify anything else
    doalt alt = return (Nothing, alt)
-- Leave all other expressions unchanged
casevalsimpl expr = return expr
-- Perform this transform everywhere
casevalsimpltop = everywhere ("casevalsimpl", casevalsimpl)

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
-- Application simplification
--------------------------------
-- Make sure that all arguments in an application are simple variables.
appsimpl, appsimpltop :: Transform
-- Don't simplify arguments that are already simple
appsimpl expr@(App f (Var _)) = return expr
-- Simplify all non-applicable (to prevent loops with inlinefun) arguments,
-- except for type arguments (since a let can't bind type vars, only a lambda
-- can). Do this by introducing a new Let that binds the argument and passing
-- the new binder in the application.
appsimpl (App f expr) | (not $ is_applicable expr) && (not $ CoreSyn.isTypeArg expr) = do
  id <- mkInternalVar "arg" (CoreUtils.exprType expr)
  change $ Let (Rec [(id, expr)]) (App f (Var id))
-- Leave all other expressions unchanged
appsimpl expr = return expr
-- Perform this transform everywhere
appsimpltop = everywhere ("appsimpl", appsimpl)


--------------------------------
-- Type argument propagation
--------------------------------
-- Remove all applications to type arguments, by duplicating the function
-- called with the type application in its new definition. We leave
-- dictionaries that might be associated with the type untouched, the funprop
-- transform should propagate these later on.
typeprop, typeproptop :: Transform
-- Transform any function that is applied to a type argument. Since type
-- arguments are always the first ones to apply and we'll remove all type
-- arguments, we can simply do them one by one. We only propagate type
-- arguments without any free tyvars, since tyvars those wouldn't be in scope
-- in the new function.
typeprop expr@(App (Var f) arg@(Type ty)) | not $ has_free_tyvars arg = do
  body_maybe <- Trans.lift $ getGlobalBind f
  case body_maybe of
    Just body -> do
      let newbody = App body (Type ty)
      -- Create a new function with the same name but a new body
      newf <- mkFunction f newbody
      -- Replace the application with this new function
      change (Var newf)
    -- If we don't have a body for the function called, leave it unchanged (it
    -- should be a primitive function then).
    Nothing -> return expr
-- Leave all other expressions unchanged
typeprop expr = return expr
-- Perform this transform everywhere
typeproptop = everywhere ("typeprop", typeprop)


--------------------------------
-- Function-typed argument propagation
--------------------------------
-- Remove all applications to function-typed arguments, by duplication the
-- function called with the function-typed parameter replaced by the free
-- variables of the argument passed in.
funprop, funproptop :: Transform
-- Transform any application of a named function (i.e., skip applications of
-- lambda's). Also skip applications that have arguments with free type
-- variables, since we can't inline those.
funprop expr@(App _ _) | is_var fexpr && not (any has_free_tyvars args) = do
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
          newf <- mkFunction f newbody
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
    doarg arg | is_fun arg = do
      bndrs <- Trans.lift getGlobalBinders
      -- Find interesting free variables, each of which should be passed to
      -- the new function instead of the original function argument.
      -- 
      -- Interesting vars are those that are local, but not available from the
      -- top level scope (functions from this module are defined as local, but
      -- they're not local to this function, so we can freely move references
      -- to them into another function).
      let interesting var = Var.isLocalVar var && (not $ var `elem` bndrs)
      let free_vars = VarSet.varSetElems $ CoreFVs.exprSomeFreeVars interesting arg
      -- Mark the current expression as changed
      setChanged
      return (map Var free_vars, free_vars, arg)
    -- Non-functiontyped arguments can be unchanged. Note that this handles
    -- both values and types.
    doarg arg = do
      -- TODO: preserve original naming?
      id <- mkBinderFor arg "param"
      -- Just pass the original argument to the new function, which binds it
      -- to a new id and just pass that new id to the old function body.
      return ([arg], [id], mkReferenceTo id) 
-- Leave all other expressions unchanged
funprop expr = return expr
-- Perform this transform everywhere
funproptop = everywhere ("funprop", funprop)


-- TODO: introduce top level let if needed?

--------------------------------
-- End of transformations
--------------------------------




-- What transforms to run?
transforms = [typeproptop, funproptop, etatop, betatop, letremovetop, letrectop, letsimpltop, letflattop, casewildtop, scrutsimpltop, casevalsimpltop, caseremovetop, inlinefuntop, appsimpltop]

-- Turns the given bind into VHDL
normalizeModule :: 
  UniqSupply.UniqSupply -- ^ A UniqSupply we can use
  -> [(CoreBndr, CoreExpr)]  -- ^ All bindings we know (i.e., in the current module)
  -> [CoreBndr]  -- ^ The bindings to generate VHDL for (i.e., the top level bindings)
  -> [Bool] -- ^ For each of the bindings to generate VHDL for, if it is stateful
  -> [(CoreBndr, CoreExpr)] -- ^ The resulting VHDL

normalizeModule uniqsupply bindings generate_for statefuls = runTransformSession uniqsupply $ do
  -- Put all the bindings in this module in the tsBindings map
  putA tsBindings (Map.fromList bindings)
  -- (Recursively) normalize each of the requested bindings
  mapM normalizeBind generate_for
  -- Get all initial bindings and the ones we produced
  bindings_map <- getA tsBindings
  let bindings = Map.assocs bindings_map
  normalized_bindings <- getA tsNormalized
  -- But return only the normalized bindings
  return $ filter ((flip VarSet.elemVarSet normalized_bindings) . fst) bindings

normalizeBind :: CoreBndr -> TransformSession ()
normalizeBind bndr =
  -- Skip binders that have a polymorphic type, since it's impossible to
  -- create polymorphic hardware.
  if is_poly (Var bndr)
    then
      -- This should really only happen at the top level... TODO: Give
      -- a different error if this happens down in the recursion.
      error $ "Function " ++ show bndr ++ " is polymorphic, can't normalize"
    else do
      normalized_funcs <- getA tsNormalized
      -- See if this function was normalized already
      if VarSet.elemVarSet bndr normalized_funcs
        then
          -- Yup, don't do it again
          return ()
        else do
          -- Nope, note that it has been and do it.
          modA tsNormalized (flip VarSet.extendVarSet bndr)
          expr_maybe <- getGlobalBind bndr
          case expr_maybe of 
            Just expr -> do
              -- Introduce an empty Let at the top level, so there will always be
              -- a let in the expression (none of the transformations will remove
              -- the last let).
              let expr' = Let (Rec []) expr
              -- Normalize this expression
              trace ("Transforming " ++ (show bndr) ++ "\nBefore:\n\n" ++ showSDoc ( ppr expr ) ++ "\n") $ return ()
              expr' <- dotransforms transforms expr
              trace ("\nAfter:\n\n" ++ showSDoc ( ppr expr')) $ return ()
              -- And store the normalized version in the session
              modA tsBindings (Map.insert bndr expr')
              -- Find all vars used with a function type. All of these should be global
              -- binders (i.e., functions used), since any local binders with a function
              -- type should have been inlined already.
              let used_funcs_set = CoreFVs.exprSomeFreeVars (\v -> (Type.isFunTy . snd . Type.splitForAllTys . Id.idType) v) expr'
              let used_funcs = VarSet.varSetElems used_funcs_set
              -- Process each of the used functions recursively
              mapM normalizeBind used_funcs
              return ()
            -- We don't have a value for this binder, let's assume this is a builtin
            -- function. This might need some extra checking and a nice error
            -- message).
            Nothing -> return ()
