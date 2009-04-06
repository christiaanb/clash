{-# LANGUAGE StandaloneDeriving,FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module CoreShow where

-- This module derives Show instances for CoreSyn types.

import qualified BasicTypes

import qualified CoreSyn
import qualified TypeRep
import qualified TyCon

import qualified HsTypes
import qualified HsExpr
import qualified SrcLoc
import qualified RdrName

import Outputable ( Outputable, OutputableBndr, showSDoc, ppr)


-- Derive Show for core expressions and binders, so we can see the actual
-- structure.
deriving instance (Show b) => Show (CoreSyn.Expr b)
deriving instance (Show b) => Show (CoreSyn.Bind b)
deriving instance Show TypeRep.Type
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.HsType n)
deriving instance (Show x) => Show (SrcLoc.Located x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.StmtLR x x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.HsExpr x)
deriving instance Show (RdrName.RdrName)


-- Implement dummy shows, since deriving them will need loads of other shows
-- as well.
instance Show CoreSyn.Note where
  show n = "<note>"
instance Show TypeRep.PredType where
  show t = "_PredType:(" ++ (showSDoc $ ppr t) ++ ")"
instance Show TyCon.TyCon where
  show t = "_TyCon:(" ++ (showSDoc $ ppr t) ++ ")"
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


instance (Outputable x) => Show x where
  show x = "__" ++  (showSDoc $ ppr x) ++ "__"
