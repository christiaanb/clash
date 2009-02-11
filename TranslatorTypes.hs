--
-- Simple module providing some types used by Translator. These are in a
-- separate module to prevent circular dependencies in Pretty for example.
--
module TranslatorTypes where

import qualified Control.Monad.State as State
import qualified HscTypes
import qualified Data.Map as Map
import FlattenTypes
import HsValueMap


-- | A map from a HsFunction identifier to various stuff we collect about a
--   function along the way.
type FuncMap  = Map.Map HsFunction FuncData

-- | A signal that has been assigned a (unique) name
data NamedSignal = NamedSignal String

-- | A function in which all signals have been assigned unique names
type NamedFlatFunction = FlatFunction' NamedSignal

-- | Some stuff we collect about a function along the way.
data FuncData = FuncData {
  flatFunc :: Maybe (Either FlatFunction NamedFlatFunction)
}

data VHDLSession = VHDLSession {
  coreMod   :: HscTypes.CoreModule, -- The current module
  nameCount :: Int,             -- A counter that can be used to generate unique names
  funcs     :: FuncMap          -- A map from HsFunction to FlatFunction, HWFunction, VHDL Entity and Architecture
}

-- | Add the function to the session
addFunc :: HsFunction -> VHDLState ()
addFunc hsfunc = do
  fs <- State.gets funcs -- Get the funcs element from the session
  let fs' = Map.insert hsfunc (FuncData Nothing) fs -- Insert function
  State.modify (\x -> x {funcs = fs' })

-- | Find the given function in the current session
getFunc :: HsFunction -> VHDLState (Maybe FuncData)
getFunc hsfunc = do
  fs <- State.gets funcs -- Get the funcs element from the session
  return $ Map.lookup hsfunc fs

-- | Sets the FlatFunction for the given HsFunction in the given setting.
setFlatFunc :: HsFunction -> (Either FlatFunction NamedFlatFunction) -> VHDLState ()
setFlatFunc hsfunc flatfunc = do
  fs <- State.gets funcs -- Get the funcs element from the session
  let fs'= Map.adjust (\d -> d { flatFunc = Just flatfunc }) hsfunc fs
  State.modify (\x -> x {funcs = fs' })

getModule :: VHDLState HscTypes.CoreModule
getModule = State.gets coreMod -- Get the coreMod element from the session

type VHDLState = State.State VHDLSession

-- Makes the given name unique by appending a unique number.
-- This does not do any checking against existing names, so it only guarantees
-- uniqueness with other names generated by uniqueName.
uniqueName :: String -> VHDLState String
uniqueName name = do
  count <- State.gets nameCount -- Get the funcs element from the session
  State.modify (\s -> s {nameCount = count + 1})
  return $ name ++ "_" ++ (show count)

-- vim: set ts=8 sw=2 sts=2 expandtab:
