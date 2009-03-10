--
-- Simple module providing some types used by Translator. These are in a
-- separate module to prevent circular dependencies in Pretty for example.
--
{-# LANGUAGE TemplateHaskell #-}
module TranslatorTypes where

import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import qualified Data.Accessor.Template
import Data.Accessor

import qualified HscTypes

import qualified ForSyDe.Backend.VHDL.AST as AST

import FlattenTypes
import VHDLTypes
import HsValueMap


-- | A map from a HsFunction identifier to various stuff we collect about a
--   function along the way.
type FlatFuncMap  = Map.Map HsFunction FlatFunction

data TranslatorSession = TranslatorSession {
  tsCoreModule_ :: HscTypes.CoreModule, -- ^ The current module
  tsNameCount_ :: Int, -- ^ A counter that can be used to generate unique names
  tsFlatFuncs_ :: FlatFuncMap -- ^ A map from HsFunction to FlatFunction
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''TranslatorSession )

type TranslatorState = State.State TranslatorSession

-- vim: set ts=8 sw=2 sts=2 expandtab:
