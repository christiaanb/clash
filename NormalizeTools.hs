{-# LANGUAGE PackageImports #-}
-- 
-- This module provides functions for program transformations.
--
module NormalizeTools where
-- Standard modules
import Debug.Trace
import qualified List
import qualified Data.Monoid as Monoid
import qualified Data.Either as Either
import qualified Control.Arrow as Arrow
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.Writer as Writer
import qualified "transformers" Control.Monad.Trans as Trans
import qualified Data.Map as Map
import Data.Accessor
import Data.Accessor.MonadState as MonadState

-- GHC API
import CoreSyn
import qualified UniqSupply
import qualified Unique
import qualified OccName
import qualified Name
import qualified Var
import qualified SrcLoc
import qualified Type
import qualified IdInfo
import qualified CoreUtils
import qualified CoreSubst
import qualified VarSet
import qualified HscTypes
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import NormalizeTypes
import Pretty
import VHDLTypes
import qualified VHDLTools

-- Create a new internal var with the given name and type. A Unique is
-- appended to the given name, to ensure uniqueness (not strictly neccesary,
-- since the Unique is also stored in the name, but this ensures variable
-- names are unique in the output).
mkInternalVar :: String -> Type.Type -> TransformMonad Var.Var
mkInternalVar str ty = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc (str ++ show uniq)
  let name = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkLocalIdVar name ty IdInfo.vanillaIdInfo

-- Create a new type variable with the given name and kind. A Unique is
-- appended to the given name, to ensure uniqueness (not strictly neccesary,
-- since the Unique is also stored in the name, but this ensures variable
-- names are unique in the output).
mkTypeVar :: String -> Type.Kind -> TransformMonad Var.Var
mkTypeVar str kind = do
  uniq <- mkUnique
  let occname = OccName.mkVarOcc (str ++ show uniq)
  let name = Name.mkInternalName uniq occname SrcLoc.noSrcSpan
  return $ Var.mkTyVar name kind

-- Creates a binder for the given expression with the given name. This
-- works for both value and type level expressions, so it can return a Var or
-- TyVar (which is just an alias for Var).
mkBinderFor :: CoreExpr -> String -> TransformMonad Var.Var
mkBinderFor (Type ty) string = mkTypeVar string (Type.typeKind ty)
mkBinderFor expr string = mkInternalVar string (CoreUtils.exprType expr)

-- Creates a reference to the given variable. This works for both a normal
-- variable as well as a type variable
mkReferenceTo :: Var.Var -> CoreExpr
mkReferenceTo var | Var.isTyVar var = (Type $ Type.mkTyVarTy var)
                  | otherwise       = (Var var)

cloneVar :: Var.Var -> TransformMonad Var.Var
cloneVar v = do
  uniq <- mkUnique
  -- Swap out the unique, and reset the IdInfo (I'm not 100% sure what it
  -- contains, but vannillaIdInfo is always correct, since it means "no info").
  return $ Var.lazySetVarIdInfo (Var.setVarUnique v uniq) IdInfo.vanillaIdInfo

-- Creates a new function with the same name as the given binder (but with a
-- new unique) and with the given function body. Returns the new binder for
-- this function.
mkFunction :: CoreBndr -> CoreExpr -> TransformMonad CoreBndr
mkFunction bndr body = do
  let ty = CoreUtils.exprType body
  id <- cloneVar bndr
  let newid = Var.setVarType id ty
  Trans.lift $ addGlobalBind newid body
  return newid

-- Apply the given transformation to all expressions in the given expression,
-- including the expression itself.
everywhere :: (String, Transform) -> Transform
everywhere trans = applyboth (subeverywhere (everywhere trans)) trans

-- Apply the first transformation, followed by the second transformation, and
-- keep applying both for as long as expression still changes.
applyboth :: Transform -> (String, Transform) -> Transform
applyboth first (name, second) expr  = do
  -- Apply the first
  expr' <- first expr
  -- Apply the second
  (expr'', changed) <- Writer.listen $ second expr'
  if Monoid.getAny $
--        trace ("Trying to apply transform " ++ name ++ " to:\n" ++ showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n") $
        changed 
    then 
--      trace ("Applying transform " ++ name ++ " to:\n" ++ showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n") $
--      trace ("Result of applying " ++ name ++ ":\n" ++ showSDoc (nest 4 $ ppr expr'') ++ "\n" ++ "Type: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr'') ++ "\n" ) $
      applyboth first (name, second) $
        expr'' 
    else 
--      trace ("No changes") $
      return expr''

-- Apply the given transformation to all direct subexpressions (only), not the
-- expression itself.
subeverywhere :: Transform -> Transform
subeverywhere trans (App a b) = do
  a' <- trans a
  b' <- trans b
  return $ App a' b'

subeverywhere trans (Let (NonRec b bexpr) expr) = do
  bexpr' <- trans bexpr
  expr' <- trans expr
  return $ Let (NonRec b bexpr') expr'

subeverywhere trans (Let (Rec binds) expr) = do
  expr' <- trans expr
  binds' <- mapM transbind binds
  return $ Let (Rec binds') expr'
  where
    transbind :: (CoreBndr, CoreExpr) -> TransformMonad (CoreBndr, CoreExpr)
    transbind (b, e) = do
      e' <- trans e
      return (b, e')

subeverywhere trans (Lam x expr) = do
  expr' <- trans expr
  return $ Lam x expr'

subeverywhere trans (Case scrut b t alts) = do
  scrut' <- trans scrut
  alts' <- mapM transalt alts
  return $ Case scrut' b t alts'
  where
    transalt :: CoreAlt -> TransformMonad CoreAlt
    transalt (con, binders, expr) = do
      expr' <- trans expr
      return (con, binders, expr')

subeverywhere trans (Var x) = return $ Var x
subeverywhere trans (Lit x) = return $ Lit x
subeverywhere trans (Type x) = return $ Type x

subeverywhere trans (Cast expr ty) = do
  expr' <- trans expr
  return $ Cast expr' ty

subeverywhere trans expr = error $ "\nNormalizeTools.subeverywhere: Unsupported expression: " ++ show expr

-- Apply the given transformation to all expressions, except for direct
-- arguments of an application
notappargs :: (String, Transform) -> Transform
notappargs trans = applyboth (subnotappargs trans) trans

-- Apply the given transformation to all (direct and indirect) subexpressions
-- (but not the expression itself), except for direct arguments of an
-- application
subnotappargs :: (String, Transform) -> Transform
subnotappargs trans (App a b) = do
  a' <- subnotappargs trans a
  b' <- subnotappargs trans b
  return $ App a' b'

-- Let subeverywhere handle all other expressions
subnotappargs trans expr = subeverywhere (notappargs trans) expr

-- Runs each of the transforms repeatedly inside the State monad.
dotransforms :: [Transform] -> CoreExpr -> TransformSession CoreExpr
dotransforms transs expr = do
  (expr', changed) <- Writer.runWriterT $ Monad.foldM (flip ($)) expr transs
  if Monoid.getAny changed then dotransforms transs expr' else return expr'

-- Inline all let bindings that satisfy the given condition
inlinebind :: ((CoreBndr, CoreExpr) -> TransformMonad Bool) -> Transform
inlinebind condition expr@(Let (Rec binds) res) = do
    -- Find all bindings that adhere to the condition
    res_eithers <- mapM docond binds
    case Either.partitionEithers res_eithers of
      -- No replaces? No change
      ([], _) -> return expr
      (replace, others) -> do
        -- Substitute the to be replaced binders with their expression
        let newexpr = substitute replace (Let (Rec others) res)
        change newexpr
  where 
    docond :: (CoreBndr, CoreExpr) -> TransformMonad (Either (CoreBndr, CoreExpr) (CoreBndr, CoreExpr))
    docond b = do
      res <- condition b
      return $ case res of True -> Left b; False -> Right b

-- Leave all other expressions unchanged
inlinebind _ expr = return expr

-- Sets the changed flag in the TransformMonad, to signify that some
-- transform has changed the result
setChanged :: TransformMonad ()
setChanged = Writer.tell (Monoid.Any True)

-- Sets the changed flag and returns the given value.
change :: a -> TransformMonad a
change val = do
  setChanged
  return val

-- Create a new Unique
mkUnique :: TransformMonad Unique.Unique
mkUnique = Trans.lift $ do
    us <- getA tsUniqSupply 
    let (us', us'') = UniqSupply.splitUniqSupply us
    putA tsUniqSupply us'
    return $ UniqSupply.uniqFromSupply us''

-- Replace each of the binders given with the coresponding expressions in the
-- given expression.
substitute :: [(CoreBndr, CoreExpr)] -> CoreExpr -> CoreExpr
substitute [] expr = expr
-- Apply one substitution on the expression, but also on any remaining
-- substitutions. This seems to be the only way to handle substitutions like
-- [(b, c), (a, b)]. This means we reuse a substitution, which is not allowed
-- according to CoreSubst documentation (but it doesn't seem to be a problem).
-- TODO: Find out how this works, exactly.
substitute ((b, e):subss) expr = substitute subss' expr'
  where 
    -- Create the Subst
    subs = (CoreSubst.extendSubst CoreSubst.emptySubst b e)
    -- Apply this substitution to the main expression
    expr' = CoreSubst.substExpr subs expr
    -- Apply this substitution on all the expressions in the remaining
    -- substitutions
    subss' = map (Arrow.second (CoreSubst.substExpr subs)) subss

-- Run a given TransformSession. Used mostly to setup the right calls and
-- an initial state.
runTransformSession :: HscTypes.HscEnv -> UniqSupply.UniqSupply -> TransformSession a -> a
runTransformSession env uniqSupply session = State.evalState session emptyTransformState
  where
    emptyTypeState = TypeState Map.empty [] Map.empty Map.empty env
    emptyTransformState = TransformState uniqSupply Map.empty VarSet.emptyVarSet emptyTypeState

-- Is the given expression representable at runtime, based on the type?
isRepr :: CoreSyn.CoreExpr -> TransformMonad Bool
isRepr (Type ty) = return False
isRepr expr = Trans.lift $ MonadState.lift tsType $ VHDLTools.isReprType (CoreUtils.exprType expr)
