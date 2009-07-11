-- | This module provides a number of functions to find out things about Core
-- programs. This module does not provide the actual plumbing to work with
-- Core and Haskell (it uses HsTools for this), but only the functions that
-- know about various libraries and know which functions to call.
module CoreTools where

--Standard modules
import qualified Maybe
import System.IO.Unsafe

-- GHC API
import qualified GHC
import qualified Type
import qualified TcType
import qualified HsExpr
import qualified HsTypes
import qualified HsBinds
import qualified HscTypes
import qualified RdrName
import qualified Name
import qualified OccName
import qualified TysWiredIn
import qualified Bag
import qualified DynFlags
import qualified SrcLoc
import qualified CoreSyn
import qualified Var
import qualified VarSet
import qualified Unique
import qualified CoreUtils
import qualified CoreFVs
import qualified Literal

-- Local imports
import GhcTools
import HsTools
import Pretty

-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int.
eval_tfp_int :: Type.Type -> Int
eval_tfp_int ty =
  unsafeRunGhc $ do
    -- Automatically import modules for any fully qualified identifiers
    setDynFlag DynFlags.Opt_ImplicitImportQualified

    let from_int_t_name = mkRdrName "Types.Data.Num" "fromIntegerT"
    let from_int_t = SrcLoc.noLoc $ HsExpr.HsVar from_int_t_name
    let undef = hsTypedUndef $ coreToHsType ty
    let app = SrcLoc.noLoc $ HsExpr.HsApp (from_int_t) (undef)
    let int_ty = SrcLoc.noLoc $ HsTypes.HsTyVar TysWiredIn.intTyCon_RDR
    let expr = HsExpr.ExprWithTySig app int_ty
    let foo_name = mkRdrName "Types.Data.Num" "foo"
    let foo_bind_name = RdrName.mkRdrUnqual $ OccName.mkVarOcc "foo"
    let binds = Bag.listToBag [SrcLoc.noLoc $ HsBinds.VarBind foo_bind_name (SrcLoc.noLoc $ HsExpr.HsVar foo_name)]
    let letexpr = HsExpr.HsLet 
          (HsBinds.HsValBinds $ (HsBinds.ValBindsIn binds) [])
          (SrcLoc.noLoc expr)

    let modules = map GHC.mkModuleName ["Types.Data.Num"]
    core <- toCore modules expr
    execCore core 

normalise_tfp_int :: HscTypes.HscEnv -> Type.Type -> Type.Type
normalise_tfp_int env ty =
   unsafePerformIO $ do
     nty <- normaliseType env ty
     return nty

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

-- Is this a wild binder?
is_wild :: CoreSyn.CoreBndr -> Bool
-- wild binders have a particular unique, that we copied from MkCore.lhs to
-- here. However, this comparison didn't work, so we'll just check the
-- occstring for now... TODO
--(Var.varUnique bndr) == (Unique.mkBuiltinUnique 1)
is_wild bndr = "wild" == (OccName.occNameString . Name.nameOccName . Var.varName) bndr

-- Is the given core expression a lambda abstraction?
is_lam :: CoreSyn.CoreExpr -> Bool
is_lam (CoreSyn.Lam _ _) = True
is_lam _ = False

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

-- Does the given CoreExpr have any free local vars?
has_free_vars :: CoreSyn.CoreExpr -> Bool
has_free_vars = not . VarSet.isEmptyVarSet . CoreFVs.exprFreeVars

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

getLiterals :: CoreSyn.CoreExpr -> [CoreSyn.CoreExpr]
getLiterals app@(CoreSyn.App _ _) = literals
  where
    (CoreSyn.Var f, args) = CoreSyn.collectArgs app
    literals = filter (is_lit) args