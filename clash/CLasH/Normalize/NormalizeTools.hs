-- 
-- This module provides functions for program transformations.
--
module CLasH.Normalize.NormalizeTools where

-- Standard modules
import qualified Data.Monoid as Monoid
import qualified Data.Either as Either
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Writer as Writer
import qualified Control.Monad.Trans.Class as Trans
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState

-- GHC API
import CoreSyn
import qualified Name
import qualified Id
import qualified CoreSubst
import qualified Type
import qualified CoreUtils
import qualified TyCon
import qualified Var
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import CLasH.Normalize.NormalizeTypes
import CLasH.Translator.TranslatorTypes
import CLasH.VHDL.Constants (builtinIds)
import CLasH.Utils
import qualified CLasH.Utils.Core.CoreTools as CoreTools
import qualified CLasH.VHDL.VHDLTools as VHDLTools

-- Apply the given transformation to all expressions in the given expression,
-- including the expression itself.
everywhere :: Transform -> Transform
everywhere trans = applyboth (subeverywhere (everywhere trans)) trans

data NormDbgLevel = 
    NormDbgNone         -- ^ No debugging
  | NormDbgFinal        -- ^ Print functions before / after normalization
  | NormDbgApplied      -- ^ Print expressions before / after applying transformations
  | NormDbgAll          -- ^ Print expressions when a transformation does not apply
  deriving (Eq, Ord)
normalize_debug = NormDbgNone

-- Applies a transform, optionally showing some debug output.
apply :: (String, Transform) -> Transform
apply (name, trans) ctx expr =  do
    -- Apply the transformation and find out if it changed anything
    (expr', any_changed) <- Writer.listen $ trans ctx expr
    let changed = Monoid.getAny any_changed
    -- If it changed, increase the transformation counter 
    Monad.when changed $ Trans.lift (MonadState.modify tsTransformCounter (+1))
    -- Prepare some debug strings
    let before = showSDoc (nest 4 $ ppr expr) ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr) ++ "\n"
    let context = "Context: " ++ show ctx ++ "\n"
    let after  = showSDoc (nest 4 $ ppr expr') ++ "\nType: \n" ++ (showSDoc $ nest 4 $ ppr $ CoreUtils.exprType expr') ++ "\n"
    traceIf (normalize_debug >= NormDbgApplied && changed) ("Changes when applying transform " ++ name ++ " to:\n" ++ before ++ context ++ "Result:\n" ++ after) $ 
     traceIf (normalize_debug >= NormDbgAll && not changed) ("No changes when applying transform " ++ name ++ " to:\n" ++ before  ++ context) $
     return expr'

-- Apply the first transformation, followed by the second transformation, and
-- keep applying both for as long as expression still changes.
applyboth :: Transform -> Transform -> Transform
applyboth first second context expr = do
  -- Apply the first
  expr' <- first context expr
  -- Apply the second
  (expr'', changed) <- Writer.listen $ second context expr'
  if Monoid.getAny $ changed
    then
      applyboth first second context expr'' 
    else 
      return expr''

-- Apply the given transformation to all direct subexpressions (only), not the
-- expression itself.
subeverywhere :: Transform -> Transform
subeverywhere trans c (App a b) = do
  a' <- trans (AppFirst:c) a
  b' <- trans (AppSecond:c) b
  return $ App a' b'

subeverywhere trans c (Let (NonRec b bexpr) expr) = do
  -- In the binding of a non-recursive let binding, no extra binders are
  -- in scope.
  bexpr' <- trans (LetBinding []:c) bexpr
  -- In the body of a non-recursive let binding, the bound binder is in
  -- scope.
  expr' <- trans ((LetBody [b]):c) expr
  return $ Let (NonRec b bexpr') expr'

subeverywhere trans c (Let (Rec binds) expr) = do
  -- In the body of a recursive let, all binders are in scope
  expr' <- trans ((LetBody bndrs):c) expr
  binds' <- mapM transbind binds
  return $ Let (Rec binds') expr'
  where
    bndrs = map fst binds
    transbind :: (CoreBndr, CoreExpr) -> TransformMonad (CoreBndr, CoreExpr)
    transbind (b, e) = do
      -- In the bindings of a recursive let, all binders are in scope
      e' <- trans ((LetBinding bndrs):c) e
      return (b, e')

subeverywhere trans c (Lam x expr) = do
  -- In the body of a lambda, the bound binder is in scope.
  expr' <- trans ((LambdaBody x):c) expr
  return $ Lam x expr'

subeverywhere trans c (Case scrut b t alts) = do
  scrut' <- trans (Other:c) scrut
  alts' <- mapM transalt alts
  return $ Case scrut' b t alts'
  where
    transalt :: CoreAlt -> TransformMonad CoreAlt
    transalt (con, binders, expr) = do
      expr' <- trans ((CaseAlt b):c) expr
      return (con, binders, expr')

subeverywhere trans c (Var x) = return $ Var x
subeverywhere trans c (Lit x) = return $ Lit x
subeverywhere trans c (Type x) = return $ Type x
subeverywhere trans c (Note msg expr) = trans (Other:c) expr

subeverywhere trans c (Cast expr ty) = do
  expr' <- trans (Other:c) expr
  return $ Cast expr' ty

-- subeverywhere trans c expr = error $ "\nNormalizeTools.subeverywhere: Unsupported expression: " ++ show expr

-- Runs each of the transforms repeatedly inside the State monad.
dotransforms :: [(String, Transform)] -> CoreExpr -> TranslatorSession CoreExpr
dotransforms transs expr = do
  (expr', changed) <- Writer.runWriterT $ Monad.foldM (\e trans -> everywhere (apply trans) [] e) expr transs
  if Monoid.getAny changed then dotransforms transs expr' else return expr'

-- Inline all let bindings that satisfy the given condition
inlinebind :: ((CoreBndr, CoreExpr) -> TransformMonad Bool) -> Transform
inlinebind condition context expr@(Let (Rec binds) res) = do
    -- Find all bindings that adhere to the condition
    res_eithers <- mapM docond binds
    case Either.partitionEithers res_eithers of
      -- No replaces? No change
      ([], _) -> return expr
      (replace, others) -> do
        -- Substitute the to be replaced binders with their expression
        newexpr <- do_substitute replace (Let (Rec others) res)
        change newexpr
  where 
    -- Apply the condition to a let binding and return an Either
    -- depending on whether it needs to be inlined or not.
    docond :: (CoreBndr, CoreExpr) -> TransformMonad (Either (CoreBndr, CoreExpr) (CoreBndr, CoreExpr))
    docond b = do
      res <- condition b
      return $ case res of True -> Left b; False -> Right b

    -- Apply the given list of substitutions to the the given expression
    do_substitute :: [(CoreBndr, CoreExpr)] -> CoreExpr -> TransformMonad CoreExpr
    do_substitute [] expr = return expr
    do_substitute ((bndr, val):reps) expr = do
      -- Perform this substitution in the expression
      expr' <- substitute_clone bndr val context expr
      -- And in the substitution values we will be using next
      reps' <- mapM (subs_bind bndr val) reps
      -- And then perform the remaining substitutions
      do_substitute reps' expr'

    -- All binders bound in the transformed recursive let
    bndrs = map fst binds
   
    -- Replace the given binder with the given expression in the
    -- expression oft the given let binding
    subs_bind :: CoreBndr -> CoreExpr -> (CoreBndr, CoreExpr) -> TransformMonad (CoreBndr, CoreExpr)
    subs_bind bndr expr (b, v) = do
      v' <- substitute_clone  bndr expr ((LetBinding bndrs):context) v
      return (b, v')


-- Leave all other expressions unchanged
inlinebind _ context expr = return expr

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
substitute find repl context expr = do
  let subst = CoreSubst.extendSubst CoreSubst.emptySubst find repl
  return $ CoreSubst.substExpr subst expr 

-- | Creates a transformation that substitutes the given binder with the given
-- expression. This does only work for value expressions! All binders in the
-- expression are cloned before the replacement, to guarantee uniqueness.
substitute_clone :: CoreBndr -> CoreExpr -> Transform
-- If we see the var to find, replace it by a uniqued version of repl
substitute_clone find repl context (Var var) | find == var = do
  repl' <- Trans.lift $ CoreTools.genUniques repl
  change repl'

-- For all other expressions, just look in subexpressions
substitute_clone find repl context expr = subeverywhere (substitute_clone find repl) context expr

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
  -- A datacon id is not a global binder, but not a local variable
  -- either.
  let is_dc = Id.isDataConWorkId v
  return $ not is_dc && v `notElem` bndrs
is_local_var _ = return False

-- Is the given binder defined by the user?
isUserDefined :: CoreSyn.CoreBndr -> Bool
-- System names are certain to not be user defined
isUserDefined bndr | Name.isSystemName (Id.idName bndr) = False
-- Builtin functions are usually not user-defined either (and would
-- break currently if they are...)
isUserDefined bndr = str `notElem` builtinIds
  where
    str = Name.getOccString bndr

-- | Is the given binder normalizable? This means that its type signature can be
-- represented in hardware, which should (?) guarantee that it can be made
-- into hardware. This checks whether all the arguments and (optionally)
-- the return value are
-- representable.
isNormalizeable :: 
  Bool -- ^ Allow the result to be unrepresentable?
  -> CoreBndr  -- ^ The binder to check
  -> TranslatorSession Bool  -- ^ Is it normalizeable?
isNormalizeable result_nonrep bndr = do
  let ty = Id.idType bndr
  let (arg_tys, res_ty) = Type.splitFunTys ty
  let check_tys = if result_nonrep then arg_tys else (res_ty:arg_tys) 
  andM $ mapM isRepr' check_tys

isNormalizeableE :: 
  Bool -- ^ Allow the result to be unrepresentable?
  -> CoreExpr  -- ^ The binder to check
  -> TranslatorSession Bool  -- ^ Is it normalizeable?
isNormalizeableE result_nonrep expr = do
  let ty = CoreUtils.exprType expr
  let (arg_tys, res_ty) = Type.splitFunTys ty
  let check_tys = if result_nonrep then arg_tys else (res_ty:arg_tys) 
  andM $ mapM isRepr' check_tys

isArrowB ::
	CoreBndr
	-> Bool
isArrowB bndr = res
  where
  	ty = Id.idType bndr
  	res = case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> Name.getOccString (TyCon.tyConName tycon) == "Comp"
  		Nothing -> False

isArrowE ::
	CoreExpr
	-> Bool
isArrowE expr = res
  where
	  ty = CoreUtils.exprType expr
	  res =	case Type.splitTyConApp_maybe ty of
  		Just (tycon, args) -> (Name.getOccString (TyCon.tyConName tycon)) == "Comp"
  		Nothing -> False
	
isLift ::
	(CoreExpr, [CoreExpr])
	-> Bool
isLift ((Var bndr), args) = (Name.getOccString bndr) == "^^^" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 2
isLift _                  = False

isComponent ::
	(CoreExpr, [CoreExpr])
	-> Bool
isComponent ((Var bndr), args) = (Name.getOccString bndr) == "comp" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 3
isComponent _                  = False
	
isArrHooks ::
	(CoreExpr, [CoreExpr])
	-> Bool
isArrHooks ((Var bndr), args) = (Name.getOccString bndr) == ">>>" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 2
isArrHooks _                  = False	
	
isArrLift ::
	(CoreExpr, [CoreExpr])
	-> Bool
isArrLift ((Var bndr), args) = (Name.getOccString bndr) == "arr" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 1
isArrLift _                  = False	

isArrFirst ::
	(CoreExpr, [CoreExpr])
	-> Bool
isArrFirst ((Var bndr), args) = (Name.getOccString bndr) == "first" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 1
isArrFirst _                  = False

isArrLoop ::
	(CoreExpr, [CoreExpr])
	-> Bool
isArrLoop ((Var bndr), args) = (Name.getOccString bndr) == "loop" && (length $ CoreTools.get_val_args (Var.varType bndr) args) == 1
isArrLoop _                  = False
