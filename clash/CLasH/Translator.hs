module CLasH.Translator 
  (
   makeVHDLAnnotations
  ) where

-- Standard Modules
import qualified System.Directory as Directory
import qualified Maybe
import qualified Monad
import qualified System.FilePath as FilePath
import qualified Control.Monad.Trans.State.Strict as State
import Text.PrettyPrint.HughesPJ (render)
import Data.Accessor.Monad.Trans.StrictState
import qualified Data.Map as Map
import qualified Data.Time.Clock as Clock
import Debug.Trace

-- GHC API
import qualified CoreSyn
import qualified HscTypes
import qualified UniqSupply

-- VHDL Imports
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.FileIO as FileIO
import qualified Language.VHDL.Ppr as Ppr

-- Local Imports
import CLasH.Translator.TranslatorTypes
import CLasH.Translator.Annotations
import CLasH.Utils
import CLasH.Utils.GhcTools
import CLasH.VHDL
import CLasH.VHDL.VHDLTools
import CLasH.VHDL.Testbench

-- | Turn Haskell to VHDL, Using the Annotations for Top Entity, Initial State
--   and Test Inputs found in the Files. 
makeVHDLAnnotations :: 
  FilePath      -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The FileNames
  -> IO ()
makeVHDLAnnotations libdir filenames =
  makeVHDL libdir filenames finder
    where
      finder = findSpec (hasCLasHAnnotation isTopEntity)
                        (hasCLasHAnnotation isInitState)
                        (isCLasHAnnotation isInitState)
                        (hasCLasHAnnotation isTestInput)

-- | Turn Haskell to VHDL, using the given finder functions to find the Top
--   Entity, Initial State and Test Inputs in the Haskell Files.
makeVHDL ::
  FilePath      -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The Filenames
  -> Finder
  -> IO ()
makeVHDL libdir filenames finder = do
  start <- Clock.getCurrentTime
  -- Load the modules
  (cores, specs) <- loadModules libdir filenames (Just finder)
  -- Translate to VHDL
  vhdl <- moduleToVHDL cores specs
  -- Write VHDL to file. Just use the first entity for the name
  let top_entity = head $ Maybe.catMaybes $ map (\(t, _, _) -> t) specs
  let dir = "./vhdl/" ++ (show top_entity) ++ "/"
  prepareDir dir
  mapM_ (writeVHDL dir) vhdl
  end <- Clock.getCurrentTime
  trace ("\nTotal compilation took " ++ show (Clock.diffUTCTime end start)) $
    return ()

-- | Translate the specified entities in the given modules to VHDL.
moduleToVHDL ::
  [HscTypes.CoreModule]    -- ^ The Core Modules
  -> [EntitySpec]             -- ^ The entities to generate
  -> IO [(AST.VHDLId, AST.DesignFile)]
moduleToVHDL cores specs = do
  (vhdl, count) <- runTranslatorSession $ do
    let all_bindings = concatMap (\x -> CoreSyn.flattenBinds (HscTypes.cm_binds x)) cores
    -- Store the bindings we loaded
    tsBindings %= Map.fromList all_bindings
    -- let all_initstates = concatMap (\x -> case x of (_, Nothing, _) -> []; (_, Just inits, _) -> inits) specs 
    tsInitStates %= Map.empty
    test_binds <- catMaybesM $ Monad.mapM mkTest specs
    let topbinds = Maybe.catMaybes $ map (\(top, _, _) -> top) specs
    vhdl <- case topbinds of
      []  -> error "Could not find top entity requested"
      tops -> createDesignFiles (tops ++ test_binds)
    count <- get tsTransformCounter 
    return (vhdl, count)
  -- mapM_ (putStr . render . Ppr.ppr . snd) vhdl
  putStr $ "Total number of transformations applied: " ++ (show count) ++ "\n"
  return vhdl
  where
    mkTest :: EntitySpec -> TranslatorSession (Maybe CoreSyn.CoreBndr)
    -- Create a testbench for any entry that has test input
    mkTest (_, _, Nothing) = return Nothing
    mkTest (Nothing, _, _) = return Nothing
    mkTest (Just top, _, Just input) = do
      bndr <- createTestbench Nothing cores input top
      return $ Just bndr

-- Run the given translator session. Generates a new UniqSupply for that
-- session.
runTranslatorSession :: TranslatorSession a -> IO a
runTranslatorSession session = do
  -- Generate a UniqSupply
  -- Running 
  --    egrep -r "(initTcRnIf|mkSplitUniqSupply)" .
  -- on the compiler dir of ghc suggests that 'z' is not used to generate
  -- a unique supply anywhere.
  uniqSupply <- UniqSupply.mkSplitUniqSupply 'z'
  let init_typedecls = map (mktydecl . (Maybe.fromMaybe (error "Translator.runTranslatorSession: No builtin type found")) . snd) $ Map.toList builtin_types
  let init_typestate = TypeState builtin_types init_typedecls Map.empty Map.empty
  let init_state = TranslatorState uniqSupply init_typestate Map.empty Map.empty 0 Map.empty Map.empty Map.empty 0 Map.empty Map.empty
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
  FileIO.writeDesignFile vhdl fname

-- vim: set ts=8 sw=2 sts=2 expandtab:
