module CLasH.Translator 
  ( makeVHDLStrings
  , makeVHDLAnnotations
  ) where

-- Standard Modules
import qualified System.Directory as Directory
import qualified Maybe
import qualified Monad
import qualified System.FilePath as FilePath
import qualified Control.Monad.Trans.State as State
import Text.PrettyPrint.HughesPJ (render)
import Data.Accessor
import qualified Data.Map as Map

-- GHC API
import qualified CoreSyn
import qualified GHC
import qualified HscTypes
import qualified UniqSupply

-- VHDL Imports
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.FileIO
import qualified Language.VHDL.Ppr as Ppr

-- Local Imports
import CLasH.Normalize
import CLasH.Translator.TranslatorTypes
import CLasH.Translator.Annotations
import CLasH.Utils.Core.CoreTools
import CLasH.Utils.GhcTools
import CLasH.VHDL
import CLasH.VHDL.Testbench

-- | Turn Haskell to VHDL, Usings Strings to indicate the Top Entity, Initial
--   State and Test Inputs.
makeVHDLStrings :: 
  FilePath      -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The FileNames
  -> String     -- ^ The TopEntity
  -> String     -- ^ The InitState
  -> String     -- ^ The TestInput
  -> Bool       -- ^ Is it stateful? (in case InitState is empty)
  -> IO ()
makeVHDLStrings libdir filenames topentity initstate testinput stateful = do
  makeVHDL libdir filenames findTopEntity findInitState findTestInput stateful
    where
      findTopEntity = findBind (hasVarName topentity)
      findInitState = findBind (hasVarName initstate)
      findTestInput = findExpr (hasVarName testinput)

-- | Turn Haskell to VHDL, Using the Annotations for Top Entity, Initial State
--   and Test Inputs found in the Files. 
makeVHDLAnnotations :: 
  FilePath      -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The FileNames
  -> Bool       -- ^ Is it stateful? (in case InitState is not specified)
  -> IO ()
makeVHDLAnnotations libdir filenames stateful = do
  makeVHDL libdir filenames findTopEntity findInitState findTestInput stateful
    where
      findTopEntity = findBind (hasCLasHAnnotation isTopEntity)
      findInitState = findBind (hasCLasHAnnotation isInitState)
      findTestInput = findExpr (hasCLasHAnnotation isTestInput)

-- | Turn Haskell to VHDL, using the given finder functions to find the Top
--   Entity, Initial State and Test Inputs in the Haskell Files.
makeVHDL ::
  FilePath      -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The Filenames
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreBndr)) -- ^ The Top Entity Finder
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreBndr)) -- ^ The Init State Finder
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreExpr)) -- ^ The Test Input Finder
  -> Bool       -- ^ Indicates if it is meant to be stateful
  -> IO ()
makeVHDL libdir filenames topEntFinder initStateFinder testInputFinder stateful = do
  -- Load the modules
  (cores, top, init, test, env) <- loadModules libdir filenames topEntFinder initStateFinder testInputFinder
  -- Translate to VHDL
  vhdl <- moduleToVHDL env cores top init test stateful
  -- Write VHDL to file
  let top_entity = Maybe.fromJust $ head top
  let dir = "./vhdl/" ++ (show top_entity) ++ "/"
  prepareDir dir
  mapM (writeVHDL dir) vhdl
  return ()

-- | Translate the binds with the given names from the given core module to
--   VHDL. The Bool in the tuple makes the function stateful (True) or
--   stateless (False).
moduleToVHDL ::
  HscTypes.HscEnv             -- ^ The GHC Environment
  -> [HscTypes.CoreModule]    -- ^ The Core Modules
  -> [Maybe CoreSyn.CoreBndr] -- ^ The TopEntity
  -> [Maybe CoreSyn.CoreBndr] -- ^ The InitState
  -> [Maybe CoreSyn.CoreExpr] -- ^ The TestInput
  -> Bool                     -- ^ Is it stateful (in case InitState is not specified)
  -> IO [(AST.VHDLId, AST.DesignFile)]
moduleToVHDL env cores topbinds' init test stateful = do
  let topbinds = Maybe.catMaybes topbinds'
  let initialState = Maybe.catMaybes init
  let testInput = Maybe.catMaybes test
  vhdl <- runTranslatorSession env $ do
    let all_bindings = concat (map (\x -> CoreSyn.flattenBinds (HscTypes.cm_binds x)) cores)
    -- Store the bindings we loaded
    tsBindings %= Map.fromList all_bindings 
    test_binds <- Monad.zipWithM (createTestbench Nothing) testInput topbinds
    createDesignFiles (topbinds ++ test_binds)
  mapM (putStr . render . Ppr.ppr . snd) vhdl
  return vhdl

-- Run the given translator session. Generates a new UniqSupply for that
-- session.
runTranslatorSession :: HscTypes.HscEnv -> TranslatorSession a -> IO a
runTranslatorSession env session = do
  -- Generate a UniqSupply
  -- Running 
  --    egrep -r "(initTcRnIf|mkSplitUniqSupply)" .
  -- on the compiler dir of ghc suggests that 'z' is not used to generate
  -- a unique supply anywhere.
  uniqSupply <- UniqSupply.mkSplitUniqSupply 'z'
  let init_typestate = TypeState Map.empty [] Map.empty Map.empty env
  let init_state = TranslatorState uniqSupply init_typestate Map.empty Map.empty Map.empty Map.empty
  return $ State.evalState session init_state

-- | Prepares the directory for writing VHDL files. This means creating the
--   dir if it does not exist and removing all existing .vhdl files from it.
prepareDir :: String -> IO()
prepareDir dir = do
  -- Create the dir if needed
  Directory.createDirectoryIfMissing True dir
  -- Find all .vhdl files in the directory
  files <- Directory.getDirectoryContents dir
  let to_remove = filter ((==".vhdl") . FilePath.takeExtension) files
  -- Prepend the dirname to the filenames
  let abs_to_remove = map (FilePath.combine dir) to_remove
  -- Remove the files
  mapM_ Directory.removeFile abs_to_remove

-- | Write the given design file to a file with the given name inside the
--   given dir
writeVHDL :: String -> (AST.VHDLId, AST.DesignFile) -> IO ()
writeVHDL dir (name, vhdl) = do
  -- Find the filename
  let fname = dir ++ (AST.fromVHDLId name) ++ ".vhdl"
  -- Write the file
  Language.VHDL.FileIO.writeDesignFile vhdl fname

-- vim: set ts=8 sw=2 sts=2 expandtab:
