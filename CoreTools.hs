-- | This module provides a number of functions to find out things about Core
-- programs. This module does not provide the actual plumbing to work with
-- Core and Haskell (it uses HsTools for this), but only the functions that
-- know about various libraries and know which functions to call.
module CoreTools where
  
-- GHC API
import qualified DynFlags
import qualified Type
import qualified HsExpr
import qualified HsTypes
import qualified RdrName
import qualified HsBinds
import qualified OccName
import qualified HsBinds
import qualified SrcLoc

import qualified HsTools

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

    core <- toCore expr
    execCore core 
