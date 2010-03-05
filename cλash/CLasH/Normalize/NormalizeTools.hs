{-# LANGUAGE PackageImports #-}
-- 
-- This module provides functions for program transformations.
--
module CLasH.Normalize.NormalizeTools where

-- Standard modules
import qualified Data.Monoid as Monoid
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Writer as Writer
import qualified "transformers" Control.Monad.Trans as Trans
import qualified Data.Accessor.Monad.Trans.State as MonadState
-- import Debug.Trace

-- GHC API
import CoreSyn
import qualified Name
import qualified Id
import qualified CoreSubst
import qualified Type
-- import qualified CoreUtils
-- import Outputable ( showSDoc, ppr, nest )

-- Local imports
import CLasH.Normalize.NormalizeTypes
import CLasH.Translator.TranslatorTypes
import CLasH.Utils
import qualified CLasH.Utils.Core.CoreTools as CoreTools
import qualified CLasH.VHDL.VHDLTools as VHDLTools

-- Apply the given transformation to all expressions in the given expression,
-- including the expression itself.
everywhere :: (String, Transform) -> Transform
everywhere trans = applyboth (subeverywhere (everywhere trans)) trans

-- Apply the first transformation, followed by the second transformation, and
-- keep applying both for as long as expression still changes.
applyboth :: Transform -> (String, Transform) -> Transform
applyboth first (name, second) expr = do
  -- Apply the first
  expr' <- first expr
  -- Apply the second
  (expr'', changed) <- Writer.listen $ second expr'
  if Monoid.getAny $
        -- trace ("Trying to apply transform " ++ name ++ " to:\n" ++ showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n")
        changed 
    then 
     -- trace ("Applying transform " ++ name ++ " to:\n" ++ showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n") $
     -- trace ("Result of applying " ++ name ++ ":\n" ++ showSDoc (nest 4 $ ppr expr'') ++ "\n" ++ "Type: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr'') ++ "\n" ) $
      applyboth first (name, second)
        expr'' 
    else 
      -- trace ("No changes") $
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
dotransforms :: [Transform] -> CoreExpr -> TranslatorSession CoreExpr
dotransforms transs expr = do
  (expr', changed) <- Writer.runWriterT $ Monad.foldM (flip ($)) expr transs
  if Monoid.getAny changed then dotransforms transs expr' else return expr'

-- Inline all let bindings that satisfy the given condition
inlinebind :: ((CoreBndr, CoreExpr) -> TransformMonad Bool) -> Transform
inlinebind condition expr@(Let (NonRec bndr expr') res) = do
    applies <- condition (bndr, expr')
    if applies
      then do
        -- Substitute the binding in res and return that
        res' <- substitute_clone bndr expr' res
        change res'
      else
        -- Don't change this let
        return expr
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

-- Returns the given value and sets the changed flag if the bool given is
-- True. Note that this will not unset the changed flag if the bool is False.
changeif :: Bool -> a -> TransformMonad a
changeif True val = change val
changeif False val = return val

-- | Creates a transformation that substitutes the given binder with the given
-- expression (This can be a type variable, replace by a Type expression).
-- Does not set the changed flag.
substitute :: CoreBndr -> CoreExpr -> Transform
-- Use CoreSubst to subst a type var in an expression
substitute find repl expr = do
  let subst = CoreSubst.extendSubst CoreSubst.emptySubst find repl
  return $ CoreSubst.substExpr subst expr 

-- | Creates a transformation that substitutes the given binder with the given
-- expression. This does only work for value expressions! All binders in the
-- expression are cloned before the replacement, to guarantee uniqueness.
substitute_clone :: CoreBndr -> CoreExpr -> Transform
-- If we see the var to find, replace it by a uniqued version of repl
substitute_clone find repl (Var var) | find == var = do
  repl' <- Trans.lift $ CoreTools.genUniques repl
  change repl'

-- For all other expressions, just look in subexpressions
substitute_clone find repl expr = subeverywhere (substitute_clone find repl) expr

-- Is the given expression representable at runtime, based on the type?
isRepr :: (CoreTools.TypedThing t) => t -> TransformMonad Bool
isRepr tything = Trans.lift (isRepr' tything)

isRepr' :: (CoreTools.TypedThing t) => t -> TranslatorSession Bool
isRepr' tything = case CoreTools.getType tything of
  Nothing -> return False
  Just ty -> MonadState.lift tsType $ VHDLTools.isReprType ty 

is_local_var :: CoreSyn.CoreExpr -> TranslatorSession Bool
is_local_var (CoreSyn.Var v) = do
  bndrs <- getGlobalBinders
  return $ v `notElem` bndrs
is_local_var _ = return False

-- Is the given binder defined by the user?
isUserDefined :: CoreSyn.CoreBndr -> Bool
-- System names are certain to not be user defined
isUserDefined bndr | Name.isSystemName (Id.idName bndr) = False
-- Check a list of typical compiler-defined names
isUserDefined bndr = str `notElem` compiler_names
  where
    str = Name.getOccString bndr
    -- These are names of bindings usually generated by the compiler. For some
    -- reason these are not marked as system, probably because the name itself
    -- is not made up by the compiler, just this particular binding is.
    compiler_names = ["fromInteger", "head", "tail", "init", "last", "+", "*", "-", "!"]

-- Is the given binder normalizable? This means that its type signature can be
-- represented in hardware, which should (?) guarantee that it can be made
-- into hardware. Note that if a binder is not normalizable, it might become
-- so using argument propagation.
isNormalizeable :: CoreBndr -> TransformMonad Bool 
isNormalizeable bndr = do
  let ty = Id.idType bndr
  let (arg_tys, res_ty) = Type.splitFunTys ty
  -- This function is normalizable if all its arguments and return value are
  -- representable.
  andM $ mapM isRepr (res_ty:arg_tys)
