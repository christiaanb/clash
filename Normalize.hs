--
-- Functions to bring a Core expression in normal form. This module provides a
-- top level function "normalize", and defines the actual transformation passes that
-- are performed.
--
module Normalize (normalize) where

-- Standard modules
import Debug.Trace
import qualified List
import qualified Maybe
import qualified Control.Monad as Monad

-- GHC API
import CoreSyn
import qualified UniqSupply
import qualified CoreUtils
import qualified Type
import qualified Id
import qualified CoreSubst
import Outputable ( showSDoc, ppr, nest )

-- Local imports
import NormalizeTypes
import NormalizeTools
import CoreTools

-- What transforms to run?
transforms = []

-- Normalize a core expression by running transforms until none applies
-- anymore. Uses a UniqSupply to generate new identifiers.
normalize :: UniqSupply.UniqSupply -> CoreExpr -> CoreExpr
normalize = dotransforms transforms

