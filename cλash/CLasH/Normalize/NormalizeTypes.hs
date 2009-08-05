{-# LANGUAGE TemplateHaskell #-}
module CLasH.Normalize.NormalizeTypes where


-- Standard modules
import qualified Control.Monad.Trans.Writer as Writer
import qualified Control.Monad.Trans.State as State
import qualified Data.Monoid as Monoid
import qualified Data.Accessor.Template
import Data.Accessor
import qualified Data.Map as Map
import Debug.Trace

-- GHC API
import CoreSyn
import qualified VarSet
import Outputable ( Outputable, showSDoc, ppr )

-- Local imports
import CLasH.Utils.Core.CoreShow
import CLasH.Utils.Pretty
import CLasH.Translator.TranslatorTypes

-- Wrap a writer around a TranslatorSession, to run a single transformation
-- over a single expression and track if the expression was changed.
type TransformMonad = Writer.WriterT Monoid.Any TranslatorSession

-- | Transforms a CoreExpr and keeps track if it has changed.
type Transform = CoreExpr -> TransformMonad CoreExpr
