{-# LANGUAGE StandaloneDeriving,FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
--
-- This module derives Show instances for CoreSyn types.
--
module CLasH.Utils.Core.CoreShow where

-- GHC API
import qualified BasicTypes
import qualified CoreSyn
import qualified TypeRep
import qualified TyCon
import qualified HsTypes
import qualified HsExpr
import qualified HsBinds
import qualified SrcLoc
import qualified RdrName
import Outputable ( Outputable, OutputableBndr, showSDoc, ppr)

-- Derive Show for core expressions and binders, so we can see the actual
-- structure.
deriving instance (Show b) => Show (CoreSyn.Expr b)
deriving instance (Show b) => Show (CoreSyn.Bind b)
deriving instance Show TypeRep.Type
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.HsType n)
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.ConDeclField n)
deriving instance (Show x) => Show (SrcLoc.Located x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.StmtLR x x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.HsTupArg x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.HsExpr x)
deriving instance Show (RdrName.RdrName)
deriving instance (Show idL, Show idR, OutputableBndr idL, OutputableBndr idR) => Show (HsBinds.HsBindLR idL idR)
deriving instance Show CoreSyn.Note
deriving instance Show TyCon.SynTyConRhs


-- Implement dummy shows, since deriving them will need loads of other shows
-- as well.
instance Show TypeRep.PredType where
  show t = "_PredType:(" ++ showSDoc (ppr t) ++ ")"
instance Show TyCon.TyCon where
  show t | TyCon.isAlgTyCon t && not (TyCon.isTupleTyCon t) =
           showtc "AlgTyCon" ""
         | TyCon.isCoercionTyCon t =
           showtc "CoercionTyCon" ""
         | TyCon.isSynTyCon t =
           showtc "SynTyCon" (", synTcRhs = " ++ synrhs)
         | TyCon.isTupleTyCon t =
           showtc "TupleTyCon" ""
         | TyCon.isFunTyCon t =
           showtc "FunTyCon" ""
         | TyCon.isPrimTyCon t =
           showtc "PrimTyCon" ""
         | TyCon.isSuperKindTyCon t =
           showtc "SuperKindTyCon" ""
         | otherwise = 
           "_Nonexistant tycon?:(" ++ showSDoc (ppr t) ++ ")_"
      where
        showtc con extra = "(" ++ con ++ " {tyConName = " ++ name ++ extra ++ ", ...})"
        name = show (TyCon.tyConName t)
        synrhs = show (TyCon.synTyConRhs t)
instance Show BasicTypes.Boxity where
  show b = "_Boxity"
instance Show HsTypes.HsExplicitForAll where
  show b = "_HsExplicitForAll"
instance Show HsExpr.HsArrAppType where
  show b = "_HsArrAppType"
instance Show (HsExpr.MatchGroup x) where
  show b = "_HsMatchGroup"
instance Show (HsExpr.GroupByClause x) where
  show b = "_GroupByClause"
instance Show (HsExpr.HsStmtContext x) where
  show b = "_HsStmtContext"
instance Show (HsBinds.Prag) where
  show b = "_Prag"
instance Show (HsExpr.GRHSs id) where
  show b = "_GRHSs"


instance (Outputable x) => Show x where
  show x = "__" ++ showSDoc (ppr x) ++ "__"
