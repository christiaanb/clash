module CLasH.Translator where

import qualified GHC.Paths
import qualified "clash" CLasH.Translator as Original (makeVHDLStrings, makeVHDLAnnotations)

-- | Turn Haskell to VHDL, Usings Strings to indicate the Top Entity, Initial
--   State and Test Inputs.
makeVHDLStrings ::
  -> [FilePath] -- ^ The FileNames
  -> String     -- ^ The TopEntity
  -> String     -- ^ The InitState
  -> String     -- ^ The TestInput
  -> Bool       -- ^ Is it stateful? (in case InitState is empty)
  -> IO ()
makeVHDLStrings filenames topentity initstate testinput stateful = do
  let libdir = GHC.Paths.libdir
  Original.makeVHDLStrings libdir filenames topentity initstate testinput stateful
  
-- | Turn Haskell to VHDL, Using the Annotations for Top Entity, Initial State
--   and Test Inputs found in the Files. 
makeVHDLAnnotations ::
  -> [FilePath] -- ^ The FileNames
  -> Bool       -- ^ Is it stateful? (in case InitState is not specified)
  -> IO ()
makeVHDLAnnotations libdir filenames stateful = do
  let libdir = GHC.Paths.libdir
  Original.makeVHDLAnnotations libdir filenames stateful
