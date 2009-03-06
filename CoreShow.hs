{-# LANGUAGE StandaloneDeriving #-}
module CoreShow where

-- This module derives Show instances for CoreSyn types.

import qualified CoreSyn
import qualified TypeRep

import Outputable ( showSDoc, ppr)


-- Derive Show for core expressions and binders, so we can see the actual
-- structure.
deriving instance (Show b) => Show (CoreSyn.Expr b)
deriving instance (Show b) => Show (CoreSyn.Bind b)

-- Implement dummy shows for Note and Type, so we can at least use show on
-- expressions.
instance Show CoreSyn.Note where
  show n = "<note>"
instance Show TypeRep.Type where
  show t = "_type:(" ++ (showSDoc $ ppr t) ++ ")"
