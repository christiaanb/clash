{-# LANGUAGE ScopedTypeVariables, RankNTypes, FlexibleContexts #-}

module CLasH.Translator (makeVHDLStrings, makeVHDLAnnotations) where

-- Standard Modules
import qualified Directory
import qualified Maybe
import qualified Monad
import qualified System.FilePath as FilePath
import Text.PrettyPrint.HughesPJ (render)

-- GHC API
import qualified Annotations
import CoreSyn
import DynFlags ( defaultDynFlags )
import GHC hiding (loadModule, sigName)
import qualified HscTypes
import HscTypes ( cm_binds, cm_types )
import Name
import qualified Serialized
import qualified UniqSupply
import qualified Var

-- VHDL Imports
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.FileIO
import qualified Language.VHDL.Ppr as Ppr

-- Local Imports
import CLasH.Translator.Annotations
import CLasH.Normalize
import CLasH.Utils.Core.CoreTools
import CLasH.VHDL

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
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreBndr)) -- ^ The Top Entity Finder
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreBndr)) -- ^ The Init State Finder
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreExpr)) -- ^ The Test Input Finder
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
  HscTypes.HscEnv           -- ^ The GHC Environment
  -> [HscTypes.CoreModule]  -- ^ The Core Modules
  -> [Maybe CoreBndr]       -- ^ The TopEntity
  -> [Maybe CoreBndr]       -- ^ The InitState
  -> [Maybe CoreExpr]       -- ^ The TestInput
  -> Bool                   -- ^ Is it stateful (in case InitState is not specified)
  -> IO [(AST.VHDLId, AST.DesignFile)]
moduleToVHDL env cores top init test stateful = do
  let topEntity = Maybe.catMaybes top
  case topEntity of
    [] -> error "Top Entity Not Found"
    [topEnt] -> do
      let initialState = Maybe.catMaybes init
      let isStateful = not (null initialState) || stateful
      let testInput = Maybe.catMaybes test
      uniqSupply <- UniqSupply.mkSplitUniqSupply 'z'
      let all_bindings = concat (map (\x -> CoreSyn.flattenBinds (cm_binds x)) cores)
      let testexprs = case testInput of [] -> [] ; [x] -> reduceCoreListToHsList x
      let (normalized_bindings, test_bindings, typestate) = normalizeModule env uniqSupply all_bindings testexprs [topEnt] [isStateful]
      let vhdl = createDesignFiles typestate normalized_bindings topEnt test_bindings
      mapM (putStr . render . Ppr.ppr . snd) vhdl
      return vhdl
    xs -> error "More than one topentity found"

-- | Prepares the directory for writing VHDL files. This means creating the
--   dir if it does not exist and removing all existing .vhdl files from it.
prepareDir :: String -> IO()
prepareDir dir = do
  -- Create the dir if needed
  exists <- Directory.doesDirectoryExist dir
  Monad.unless exists $ Directory.createDirectory dir
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

-- | Loads the given files and turns it into a core module
loadModules ::
  FilePath      -- ^ The GHC Library directory 
  -> [String]   -- ^ The files that need to be loaded
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreBndr)) -- ^ The TopEntity finder
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreBndr)) -- ^ The InitState finder
  -> (HscTypes.CoreModule -> Ghc (Maybe CoreExpr)) -- ^ The TestInput finder
  -> IO ( [HscTypes.CoreModule] -- ^ The loaded modules
        , [Maybe CoreBndr]  -- ^ The TopEntity
        , [Maybe CoreBndr]  -- ^ The InitState
        , [Maybe CoreExpr]  -- ^ The TestInput
        , HscTypes.HscEnv   -- ^ The Environment corresponding ot the loaded modules 
        )
loadModules libdir filenames topEntLoc initSLoc testLoc =
  defaultErrorHandler defaultDynFlags $ do
    runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      setSessionDynFlags dflags
      cores <- mapM GHC.compileToCoreModule filenames
      env <- GHC.getSession
      top_entity <- mapM topEntLoc cores
      init_state <- mapM initSLoc cores
      test_input <- mapM testLoc cores
      return (cores, top_entity, init_state, test_input, env)

-- | Find a binder in module according to a certain criteria
findBind :: 
  GhcMonad m =>           -- ^ Expected to be run in some kind of GHC Monad
  (Var.Var -> m Bool)     -- ^ The criteria to filter the binds on
  -> HscTypes.CoreModule  -- ^ The module to be inspected
  -> m (Maybe CoreBndr)   -- ^ The (first) bind to meet the criteria
findBind annotation core = do
  let binds = CoreSyn.flattenBinds $ cm_binds core
  annbinds <- Monad.filterM (annotation . fst) binds
  let bndr = case annbinds of [] -> Nothing ; xs -> Just $ head $ fst (unzip annbinds)
  return bndr

-- | Find an expresion in module according to a certain criteria  
findExpr :: 
  GhcMonad m =>           -- ^ Expected to be run in some kind off GHC Monad
  (Var.Var -> m Bool)     -- ^ The criteria to filter the binds on
  -> HscTypes.CoreModule  -- ^ The module to be inspected
  -> m (Maybe CoreExpr)   -- ^ The (first) expr to meet the criteria
findExpr annotation core = do
  let binds = CoreSyn.flattenBinds $ cm_binds core
  annbinds <- Monad.filterM (annotation . fst) binds
  let exprs = case annbinds of [] -> Nothing ; xs -> Just $ head $ snd (unzip annbinds)
  return exprs

-- | Determine if a binder has an Annotation meeting a certain criteria
hasCLasHAnnotation ::
  GhcMonad m =>       -- ^ Expected to be run in some kind of GHC Monad
  (CLasHAnn -> Bool)  -- ^ The criteria the Annotation has to meet
  -> Var.Var          -- ^ The Binder
  -> m Bool           -- ^ Indicates if binder has the Annotation
hasCLasHAnnotation clashAnn var = do
  let deserializer = Serialized.deserializeWithData
  let target = Annotations.NamedTarget (Var.varName var)
  (anns :: [CLasHAnn]) <- GHC.findGlobalAnns deserializer target
  let annEnts = filter clashAnn anns
  case annEnts of
    [] -> return False
    xs -> return True

-- | Determine if a binder has a certain name
hasVarName ::   
  GhcMonad m => -- ^ Exprected to be run in some kind of GHC Monad
  String        -- ^ The name the binder has to have
  -> Var.Var    -- ^ The Binder
  -> m Bool     -- ^ Indicate if the binder has the name
hasVarName lookfor bind = return $ lookfor == (occNameString $ nameOccName $ getName bind)

-- vim: set ts=8 sw=2 sts=2 expandtab:
