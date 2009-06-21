{-# LANGUAGE PackageImports #-}
-- 
-- This module provides functions for program transformations.
--
module NormalizeTools where
-- Standard modules
import Debug.Trace
import qualified List
import qualified Data.Monoid as Monoid
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.Writer as Writer
import qualified "transformers" Control.Monad.Trans as Trans
import qualified Data.Map as Map
import Data.Accessor

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
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import NormalizeTypes

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

cloneVar :: Var.Var -> TransformMonad Var.Var
cloneVar v = do
  uniq <- mkUnique
  -- Swap out the unique, and reset the IdInfo (I'm not 100% sure what it
  -- contains, but vannillaIdInfo is always correct, since it means "no info").
  return $ Var.lazySetVarIdInfo (Var.setVarUnique v uniq) IdInfo.vanillaIdInfo

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
  if Monoid.getAny changed 
    then 
      trace ("Transform " ++ name ++ " changed from:\n" ++ showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n" ++ "\nTo:\n" ++ showSDoc (nest 4 $ ppr expr'') ++ "\n" ++ "Type: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr'') ++ "\n" ) $
      applyboth first (name, second) expr'' 
    else 
      return expr''

-- Apply the given transformation to all direct subexpressions (only), not the
-- expression itself.
subeverywhere :: Transform -> Transform
subeverywhere trans (App a b) = do
  a' <- trans a
  b' <- trans b
  return $ App a' b'

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
      

subeverywhere trans expr = return expr

-- Apply the given transformation to all expressions, except for every first
-- argument of an application.
notapplied :: (String, Transform) -> Transform
notapplied trans = applyboth (subnotapplied trans) trans

-- Apply the given transformation to all (direct and indirect) subexpressions
-- (but not the expression itself), except for the first argument of an
-- applicfirst argument of an application
subnotapplied :: (String, Transform) -> Transform
subnotapplied trans (App a b) = do
  a' <- subnotapplied trans a
  b' <- notapplied trans b
  return $ App a' b'

-- Let subeverywhere handle all other expressions
subnotapplied trans expr = subeverywhere (notapplied trans) expr

-- Runs each of the transforms repeatedly inside the State monad.
dotransforms :: [Transform] -> CoreExpr -> TransformSession CoreExpr
dotransforms transs expr = do
  (expr', changed) <- Writer.runWriterT $ Monad.foldM (flip ($)) expr transs
  if Monoid.getAny changed then dotransforms transs expr' else return expr'

-- Inline all let bindings that satisfy the given condition
inlinebind :: ((CoreBndr, CoreExpr) -> Bool) -> Transform
inlinebind condition (Let (Rec binds) expr) | not $ null replace =
    change newexpr
  where 
    -- Find all simple bindings
    (replace, others) = List.partition condition binds
    -- Substitute the to be replaced binders with their expression
    newexpr = substitute replace (Let (Rec others) expr)
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
substitute replace expr = CoreSubst.substExpr subs expr
    where subs = foldl (\s (b, e) -> CoreSubst.extendIdSubst s b e) CoreSubst.emptySubst replace

-- Run a given TransformSession. Used mostly to setup the right calls and
-- an initial state.
runTransformSession :: UniqSupply.UniqSupply -> TransformSession a -> a
runTransformSession uniqSupply session = State.evalState session initState
                       where initState = TransformState uniqSupply Map.empty VarSet.emptyVarSet
