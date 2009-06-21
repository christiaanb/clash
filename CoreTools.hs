-- | This module provides a number of functions to find out things about Core
-- programs. This module does not provide the actual plumbing to work with
-- Core and Haskell (it uses HsTools for this), but only the functions that
-- know about various libraries and know which functions to call.
module CoreTools where
  
-- GHC API
import qualified GHC
import qualified Type
import qualified HsExpr
import qualified HsTypes
import qualified HsBinds
import qualified RdrName
import qualified Name
import qualified OccName
import qualified TysWiredIn
import qualified Bag
import qualified DynFlags
import qualified SrcLoc
import qualified CoreSyn
import qualified Var
import qualified Unique
import qualified CoreUtils

import GhcTools
import HsTools

-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int.
eval_tfp_int :: Type.Type -> Int
eval_tfp_int ty =
  unsafeRunGhc $ do
    -- Automatically import modules for any fully qualified identifiers
    setDynFlag DynFlags.Opt_ImplicitImportQualified
    --setDynFlag DynFlags.Opt_D_dump_if_trace

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

-- | Get the width of a SizedWord type
sized_word_len :: Type.Type -> Int
sized_word_len ty =
  eval_tfp_int len
  where 
    (tycon, args) = Type.splitTyConApp ty
    [len] = args

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
tfvec_len :: Type.Type -> Int
tfvec_len ty =
  eval_tfp_int len
  where 
    (tycon, args) = Type.splitTyConApp ty
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
