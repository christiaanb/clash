{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | This module provides a number of functions to find out things about Core
-- programs. This module does not provide the actual plumbing to work with
-- Core and Haskell (it uses HsTools for this), but only the functions that
-- know about various libraries and know which functions to call.
module CLasH.Utils.Core.CoreTools where

--Standard modules
import qualified Maybe
import qualified System.IO.Unsafe

-- GHC API
import qualified GHC
import qualified Type
import qualified TcType
import qualified HsExpr
import qualified HsTypes
import qualified HscTypes
import qualified Name
import qualified Id
import qualified TyCon
import qualified DataCon
import qualified TysWiredIn
import qualified DynFlags
import qualified SrcLoc
import qualified CoreSyn
import qualified Var
import qualified IdInfo
import qualified VarSet
import qualified CoreUtils
import qualified CoreFVs
import qualified Literal
import qualified MkCore
import qualified VarEnv

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.Utils.GhcTools
import CLasH.Utils.HsTools
import CLasH.Utils.Pretty
import CLasH.Utils
import qualified CLasH.Utils.Core.BinderTools as BinderTools

-- | A single binding, used as a shortcut to simplify type signatures.
type Binding = (CoreSyn.CoreBndr, CoreSyn.CoreExpr)

-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int.
eval_tfp_int :: HscTypes.HscEnv -> Type.Type -> Int
eval_tfp_int env ty =
  unsafeRunGhc libdir $ do
    GHC.setSession env
    -- Automatically import modules for any fully qualified identifiers
    setDynFlag DynFlags.Opt_ImplicitImportQualified

    let from_int_t_name = mkRdrName "Types.Data.Num.Ops" "fromIntegerT"
    let from_int_t = SrcLoc.noLoc $ HsExpr.HsVar from_int_t_name
    let undef = hsTypedUndef $ coreToHsType ty
    let app = SrcLoc.noLoc $ HsExpr.HsApp (from_int_t) (undef)
    let int_ty = SrcLoc.noLoc $ HsTypes.HsTyVar TysWiredIn.intTyCon_RDR
    let expr = HsExpr.ExprWithTySig app int_ty
    core <- toCore expr
    execCore core
  where
    libdir = DynFlags.topDir dynflags
    dynflags = HscTypes.hsc_dflags env

normalise_tfp_int :: HscTypes.HscEnv -> Type.Type -> Type.Type
normalise_tfp_int env ty =
   System.IO.Unsafe.unsafePerformIO $
     normaliseType env ty

-- | Get the width of a SizedWord type
-- sized_word_len :: HscTypes.HscEnv -> Type.Type -> Int
-- sized_word_len env ty = eval_tfp_int env (sized_word_len_ty ty)
    
sized_word_len_ty :: Type.Type -> Type.Type
sized_word_len_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.sized_word_len_ty: Not a sized word type: " ++ (pprString ty)
    [len]         = args

-- | Get the width of a SizedInt type
-- sized_int_len :: HscTypes.HscEnv -> Type.Type -> Int
-- sized_int_len env ty = eval_tfp_int env (sized_int_len_ty ty)

sized_int_len_ty :: Type.Type -> Type.Type
sized_int_len_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.sized_int_len_ty: Not a sized int type: " ++ (pprString ty)
    [len]         = args
    
-- | Get the upperbound of a RangedWord type
-- ranged_word_bound :: HscTypes.HscEnv -> Type.Type -> Int
-- ranged_word_bound env ty = eval_tfp_int env (ranged_word_bound_ty ty)
    
ranged_word_bound_ty :: Type.Type -> Type.Type
ranged_word_bound_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.ranged_word_bound_ty: Not a sized word type: " ++ (pprString ty)
    [len]         = args

-- | Evaluate a core Type representing type level int from the TypeLevel
-- library to a real int.
-- eval_type_level_int :: Type.Type -> Int
-- eval_type_level_int ty =
--   unsafeRunGhc $ do
--     -- Automatically import modules for any fully qualified identifiers
--     setDynFlag DynFlags.Opt_ImplicitImportQualified
-- 
--     let to_int_name = mkRdrName "Data.TypeLevel.Num.Sets" "toInt"
--     let to_int = SrcLoc.noLoc $ HsExpr.HsVar to_int_name
--     let undef = hsTypedUndef $ coreToHsType ty
--     let app = HsExpr.HsApp (to_int) (undef)
-- 
--     core <- toCore [] app
--     execCore core 

-- | Get the length of a FSVec type
-- tfvec_len :: HscTypes.HscEnv -> Type.Type -> Int
-- tfvec_len env ty = eval_tfp_int env (tfvec_len_ty ty)

tfvec_len_ty :: Type.Type -> Type.Type
tfvec_len_ty ty = len
  where  
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.tfvec_len_ty: Not a vector type: " ++ (pprString ty)
    [len, el_ty] = args
    
-- | Get the element type of a TFVec type
tfvec_elem :: Type.Type -> Type.Type
tfvec_elem ty = el_ty
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.tfvec_len: Not a vector type: " ++ (pprString ty)
    [len, el_ty] = args

-- Is the given core expression a lambda abstraction?
is_lam :: CoreSyn.CoreExpr -> Bool
is_lam (CoreSyn.Lam _ _) = True
is_lam _ = False

-- Is the given core expression a let expression?
is_let :: CoreSyn.CoreExpr -> Bool
is_let (CoreSyn.Let _ _) = True
is_let _ = False

-- Is the given core expression of a function type?
is_fun :: CoreSyn.CoreExpr -> Bool
-- Treat Type arguments differently, because exprType is not defined for them.
is_fun (CoreSyn.Type _) = False
is_fun expr = (Type.isFunTy . CoreUtils.exprType) expr

-- Is the given core expression polymorphic (i.e., does it accept type
-- arguments?).
is_poly :: CoreSyn.CoreExpr -> Bool
-- Treat Type arguments differently, because exprType is not defined for them.
is_poly (CoreSyn.Type _) = False
is_poly expr = (Maybe.isJust . Type.splitForAllTy_maybe . CoreUtils.exprType) expr

-- Is the given core expression a variable reference?
is_var :: CoreSyn.CoreExpr -> Bool
is_var (CoreSyn.Var _) = True
is_var _ = False

is_lit :: CoreSyn.CoreExpr -> Bool
is_lit (CoreSyn.Lit _) = True
is_lit _ = False

-- Can the given core expression be applied to something? This is true for
-- applying to a value as well as a type.
is_applicable :: CoreSyn.CoreExpr -> Bool
is_applicable expr = is_fun expr || is_poly expr

-- Is the given core expression a variable or an application?
is_simple :: CoreSyn.CoreExpr -> Bool
is_simple (CoreSyn.App _ _) = True
is_simple (CoreSyn.Var _) = True
is_simple (CoreSyn.Cast expr _) = is_simple expr
is_simple _ = False

-- Does the given CoreExpr have any free type vars?
has_free_tyvars :: CoreSyn.CoreExpr -> Bool
has_free_tyvars = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars Var.isTyVar)

-- Does the given type have any free type vars?
ty_has_free_tyvars :: Type.Type -> Bool
ty_has_free_tyvars = not . VarSet.isEmptyVarSet . Type.tyVarsOfType

-- Does the given CoreExpr have any free local vars?
has_free_vars :: CoreSyn.CoreExpr -> Bool
has_free_vars = not . VarSet.isEmptyVarSet . CoreFVs.exprFreeVars

-- Does the given expression use any of the given binders?
expr_uses_binders :: [CoreSyn.CoreBndr] -> CoreSyn.CoreExpr -> Bool
expr_uses_binders bndrs = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` bndrs))

-- Turns a Var CoreExpr into the Id inside it. Will of course only work for
-- simple Var CoreExprs, not complexer ones.
exprToVar :: CoreSyn.CoreExpr -> Var.Id
exprToVar (CoreSyn.Var id) = id
exprToVar expr = error $ "\nCoreTools.exprToVar: Not a var: " ++ show expr

-- Turns a Lit CoreExpr into the Literal inside it.
exprToLit :: CoreSyn.CoreExpr -> Literal.Literal
exprToLit (CoreSyn.Lit lit) = lit
exprToLit expr = error $ "\nCoreTools.exprToLit: Not a lit: " ++ show expr

-- Removes all the type and dictionary arguments from the given argument list,
-- leaving only the normal value arguments. The type given is the type of the
-- expression applied to this argument list.
get_val_args :: Type.Type -> [CoreSyn.CoreExpr] -> [CoreSyn.CoreExpr]
get_val_args ty args = drop n args
  where
    (tyvars, predtypes, _) = TcType.tcSplitSigmaTy ty
    -- The first (length tyvars) arguments should be types, the next 
    -- (length predtypes) arguments should be dictionaries. We drop this many
    -- arguments, to get at the value arguments.
    n = length tyvars + length predtypes

getLiterals :: HscTypes.HscEnv -> CoreSyn.CoreExpr -> [CoreSyn.CoreExpr]
getLiterals _ app@(CoreSyn.App _ _) = literals
  where
    (CoreSyn.Var f, args) = CoreSyn.collectArgs app
    literals = filter (is_lit) args

getLiterals _ lit@(CoreSyn.Lit _) = [lit]

getLiterals hscenv letrec@(CoreSyn.Let (CoreSyn.NonRec letBind (letExpr)) letRes) = [lit]
  where
    ty     = Var.varType letBind
    litInt = eval_tfp_int hscenv ty
    lit    = CoreSyn.Lit (Literal.mkMachInt (toInteger litInt))

getLiterals _ expr = error $ "\nCoreTools.getLiterals: Not a known Lit: " ++ pprString expr

reduceCoreListToHsList :: 
  [HscTypes.CoreModule] -- ^ The modules where parts of the list are hidden
  -> CoreSyn.CoreExpr   -- ^ The refence to atleast one of the nodes
  -> TranslatorSession [CoreSyn.CoreExpr]
reduceCoreListToHsList cores app@(CoreSyn.App _ _) = do {
  ; let { (fun, args) = CoreSyn.collectArgs app
        ; len         = length args 
        } ;
  ; case len of
      3 -> do {
        ; let topelem = args!!1
        ; case (args!!2) of
            (varz@(CoreSyn.Var id)) -> do {
              ; binds <- mapM (findExpr (isVarName id)) cores
              ; otherelems <- reduceCoreListToHsList cores (head (Maybe.catMaybes binds))
              ; return (topelem:otherelems)
              }
            (appz@(CoreSyn.App _ _)) -> do {
              ; otherelems <- reduceCoreListToHsList cores appz
              ; return (topelem:otherelems)
              }
            otherwise -> return [topelem]
        }
      otherwise -> return []
  }
  where
    isVarName :: Monad m => Var.Var -> Var.Var -> m Bool
    isVarName lookfor bind = return $ (Var.varName lookfor) == (Var.varName bind)

reduceCoreListToHsList _ _ = return []

-- Is the given var the State data constructor?
isStateCon :: Var.Var -> Bool
isStateCon var =
  -- See if it is a DataConWrapId (not DataConWorkId, since State is a
  -- newtype).
  case Id.idDetails var of
    IdInfo.DataConWrapId dc -> 
      -- See if the datacon is the State datacon from the State type.
      let tycon = DataCon.dataConTyCon dc
          tyname = Name.getOccString tycon
          dcname = Name.getOccString dc
      in case (tyname, dcname) of
        ("State", "State") -> True
        _ -> False
    _ -> False

-- | Is the given type a State type?
isStateType :: Type.Type -> Bool
-- Resolve any type synonyms remaining
isStateType ty | Just ty' <- Type.tcView ty = isStateType ty'
isStateType ty  = Maybe.isJust $ do
  -- Split the type. Don't use normal splitAppTy, since that looks through
  -- newtypes, and we want to see the State newtype.
  (typef, _) <- Type.repSplitAppTy_maybe ty
  -- See if the applied type is a type constructor
  (tycon, _) <- Type.splitTyConApp_maybe typef
  if TyCon.isNewTyCon tycon && Name.getOccString tycon == "State"
    then
      Just ()
    else
      Nothing

-- | Does the given TypedThing have a State type?
hasStateType :: (TypedThing t) => t -> Bool
hasStateType expr = case getType expr of
  Nothing -> False
  Just ty -> isStateType ty


-- | Flattens nested lets into a single list of bindings. The expression
--   passed does not have to be a let expression, if it isn't an empty list of
--   bindings is returned.
flattenLets ::
  CoreSyn.CoreExpr -- ^ The expression to flatten.
  -> ([Binding], CoreSyn.CoreExpr) -- ^ The bindings and resulting expression.
flattenLets (CoreSyn.Let binds expr) = 
  (bindings ++ bindings', expr')
  where
    -- Recursively flatten the contained expression
    (bindings', expr') =flattenLets expr
    -- Flatten our own bindings to remove the Rec / NonRec constructors
    bindings = CoreSyn.flattenBinds [binds]
flattenLets expr = ([], expr)

-- | Create bunch of nested non-recursive let expressions from the given
-- bindings. The first binding is bound at the highest level (and thus
-- available in all other bindings).
mkNonRecLets :: [Binding] -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr
mkNonRecLets bindings expr = MkCore.mkCoreLets binds expr
  where
    binds = map (uncurry CoreSyn.NonRec) bindings

-- | A class of things that (optionally) have a core Type. The type is
-- optional, since Type expressions don't have a type themselves.
class TypedThing t where
  getType :: t -> Maybe Type.Type

instance TypedThing CoreSyn.CoreExpr where
  getType (CoreSyn.Type _) = Nothing
  getType expr = Just $ CoreUtils.exprType expr

instance TypedThing CoreSyn.CoreBndr where
  getType = return . Id.idType

instance TypedThing Type.Type where
  getType = return . id

-- | Generate new uniques for all binders in the given expression.
-- Does not support making type variables unique, though this could be
-- supported if required (by passing a CoreSubst.Subst instead of VarEnv to
-- genUniques' below).
genUniques :: CoreSyn.CoreExpr -> TranslatorSession CoreSyn.CoreExpr
genUniques = genUniques' VarEnv.emptyVarEnv

-- | A helper function to generate uniques, that takes a VarEnv containing the
--   substitutions already performed.
genUniques' :: VarEnv.VarEnv CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> TranslatorSession CoreSyn.CoreExpr
genUniques' subst (CoreSyn.Var f) = do
  -- Replace the binder with its new value, if applicable.
  let f' = VarEnv.lookupWithDefaultVarEnv subst f f
  return (CoreSyn.Var f')
-- Leave literals untouched
genUniques' subst (CoreSyn.Lit l) = return $ CoreSyn.Lit l
genUniques' subst (CoreSyn.App f arg) = do
  -- Only work on subexpressions
  f' <- genUniques' subst f
  arg' <- genUniques' subst arg
  return (CoreSyn.App f' arg')
-- Don't change type abstractions
genUniques' subst expr@(CoreSyn.Lam bndr res) | CoreSyn.isTyVar bndr = return expr
genUniques' subst (CoreSyn.Lam bndr res) = do
  -- Generate a new unique for the bound variable
  (subst', bndr') <- genUnique subst bndr
  res' <- genUniques' subst' res
  return (CoreSyn.Lam bndr' res')
genUniques' subst (CoreSyn.Let (CoreSyn.NonRec bndr bound) res) = do
  -- Make the binders unique
  (subst', bndr') <- genUnique subst bndr
  bound' <- genUniques' subst' bound
  res' <- genUniques' subst' res
  return $ CoreSyn.Let (CoreSyn.NonRec bndr' bound') res'
genUniques' subst (CoreSyn.Let (CoreSyn.Rec binds) res) = do
  -- Make each of the binders unique
  (subst', bndrs') <- mapAccumLM genUnique subst (map fst binds)
  bounds' <- mapM (genUniques' subst' . snd) binds
  res' <- genUniques' subst' res
  let binds' = zip bndrs' bounds'
  return $ CoreSyn.Let (CoreSyn.Rec binds') res'
genUniques' subst (CoreSyn.Case scrut bndr ty alts) = do
  -- Process the scrutinee with the original substitution, since non of the
  -- binders bound in the Case statement is in scope in the scrutinee.
  scrut' <- genUniques' subst scrut
  -- Generate a new binder for the scrutinee
  (subst', bndr') <- genUnique subst bndr
  -- Process each of the alts
  alts' <- mapM (doalt subst') alts
  return $ CoreSyn.Case scrut' bndr' ty alts'
  where
    doalt subst (con, bndrs, expr) = do
      (subst', bndrs') <- mapAccumLM genUnique subst bndrs
      expr' <- genUniques' subst' expr
      -- Note that we don't return subst', since bndrs are only in scope in
      -- expr.
      return (con, bndrs', expr')
genUniques' subst (CoreSyn.Cast expr coercion) = do
  expr' <- genUniques' subst expr
  -- Just process the casted expression
  return $ CoreSyn.Cast expr' coercion
genUniques' subst (CoreSyn.Note note expr) = do
  expr' <- genUniques' subst expr
  -- Just process the annotated expression
  return $ CoreSyn.Note note expr'
-- Leave types untouched
genUniques' subst expr@(CoreSyn.Type _) = return expr

-- Generate a new unique for the given binder, and extend the given
-- substitution to reflect this.
genUnique :: VarEnv.VarEnv CoreSyn.CoreBndr -> CoreSyn.CoreBndr -> TranslatorSession (VarEnv.VarEnv CoreSyn.CoreBndr, CoreSyn.CoreBndr)
genUnique subst bndr = do
  bndr' <- BinderTools.cloneVar bndr
  -- Replace all occurences of the old binder with a reference to the new
  -- binder.
  let subst' = VarEnv.extendVarEnv subst bndr bndr'
  return (subst', bndr')
