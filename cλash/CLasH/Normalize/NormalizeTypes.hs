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

-- Wrap a writer around a TransformSession, to run a single transformation
-- over a single expression and track if the expression was changed.
type TransformMonad = Writer.WriterT Monoid.Any TransformSession

-- | Transforms a CoreExpr and keeps track if it has changed.
type Transform = CoreExpr -> TransformMonad CoreExpr

-- Finds the value of a global binding, if available
getGlobalBind :: CoreBndr -> TransformSession (Maybe CoreExpr)
getGlobalBind bndr = do
  bindings <- getA tsBindings
  return $ Map.lookup bndr bindings 

-- Adds a new global binding with the given value
addGlobalBind :: CoreBndr -> CoreExpr -> TransformSession ()
addGlobalBind bndr expr = modA tsBindings (Map.insert bndr expr)

-- Returns a list of all global binders
getGlobalBinders :: TransformSession [CoreBndr]
getGlobalBinders = do
  bindings <- getA tsBindings
  return $ Map.keys bindings
