{-# LANGUAGE TemplateHaskell #-}
module NormalizeTypes where


-- Standard modules
import qualified Control.Monad.Trans.Writer as Writer
import qualified Control.Monad.Trans.State as State
import qualified Data.Monoid as Monoid
import qualified Data.Accessor.Template
import Debug.Trace

-- GHC API
import CoreSyn
import qualified UniqSupply
import Outputable ( Outputable, showSDoc, ppr )

-- Local imports
import CoreShow
import Pretty

data TransformState = TransformState {
  tsUniqSupply_ :: UniqSupply.UniqSupply
}

$( Data.Accessor.Template.deriveAccessors ''TransformState )

type TransformMonad a = Writer.WriterT Monoid.Any (State.State TransformState) a
-- | Transforms a CoreExpr and keeps track if it has changed.
type Transform = CoreExpr -> TransformMonad CoreExpr
