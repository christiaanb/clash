{-# LANGUAGE ScopedTypeVariables, RankNTypes, FlexibleContexts #-}

module CLasH.Translator where

import qualified Directory
import qualified System.FilePath as FilePath
import qualified List
import Debug.Trace
import qualified Control.Arrow as Arrow
import GHC hiding (loadModule, sigName)
import CoreSyn
import qualified CoreUtils
import qualified Var
import qualified Type
import qualified TyCon
import qualified DataCon
import qualified HscMain
import qualified SrcLoc
import qualified FastString
import qualified Maybe
import qualified Module
import qualified Data.Foldable as Foldable
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad as Monad
import Name
import qualified Data.Map as Map
import Data.Accessor
import Data.Generics
import NameEnv ( lookupNameEnv )
import qualified HscTypes
import HscTypes ( cm_binds, cm_types )
import MonadUtils ( liftIO )
import Outputable ( showSDoc, ppr, showSDocDebug )
import DynFlags ( defaultDynFlags )
import qualified UniqSupply
import List ( find )
import qualified List
import qualified Monad
import qualified Annotations
import qualified Serialized

-- The following modules come from the ForSyDe project. They are really
-- internal modules, so ForSyDe.cabal has to be modified prior to installing
-- ForSyDe to get access to these modules.
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.FileIO
import qualified Language.VHDL.Ppr as Ppr
-- This is needed for rendering the pretty printed VHDL
import Text.PrettyPrint.HughesPJ (render)

import CLasH.Translator.TranslatorTypes
import CLasH.Translator.Annotations
import CLasH.Utils.Pretty
import CLasH.Normalize
import CLasH.VHDL.VHDLTypes
import CLasH.Utils.Core.CoreTools
import qualified CLasH.VHDL as VHDL

-- | Turn Haskell to VHDL
makeVHDL :: 
  FilePath  -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The FileNames
  -> String -- ^ The TopEntity
  -> String -- ^ The InitState
  -> String -- ^ The TestInput
  -> Bool   -- ^ Is It a stateful (in case InitState is not specified)
  -> IO ()
makeVHDL libdir filenames topentity initstate testinput stateful = do
  -- Load the modules
  (core, top, init, test, env) <- loadModules libdir filenames (findBind topentity) (findBind initstate) (findExpr testinput)
  -- Translate to VHDL
  vhdl <- moduleToVHDL env core top init test stateful
  -- Write VHDL to file
  let top_entity = Maybe.fromJust $ head top
  let dir = "./vhdl/" ++ (show top_entity) ++ "/"
  prepareDir dir
  mapM (writeVHDL dir) vhdl
  return ()
  
makeVHDLAnn :: 
  FilePath  -- ^ The GHC Library Dir
  -> [FilePath] -- ^ The FileNames
  -> Bool   -- ^ Is It a stateful (in case InitState is not specified)
  -> IO ()
makeVHDLAnn libdir filenames stateful = do
  -- Load the modules
  (cores, top, init, test, env) <- loadModules libdir filenames findTopEntity findInitState findTestInput
  -- Translate to VHDL
  vhdl <- moduleToVHDL env cores top init test stateful
  -- Write VHDL to file
  let top_entity = Maybe.fromJust $ head top
  let dir = "./vhdl/" ++ (show top_entity) ++ "/"
  prepareDir dir
  mapM (writeVHDL dir) vhdl
  return ()
    where
      findTopEntity = findBindAnn (hasCLasHAnnotation isTopEntity)
      findInitState = findBindAnn (hasCLasHAnnotation isInitState)
      findTestInput = findExprAnn (hasCLasHAnnotation isTestInput)

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
      let vhdl = VHDL.createDesignFiles typestate normalized_bindings topEnt test_bindings
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
  -> IO ( [HscTypes.CoreModule] -- The loaded modules
        , [Maybe CoreBndr]  -- The TopEntity
        , [Maybe CoreBndr]  -- The InitState
        , [Maybe CoreExpr]  -- The TestInput
        , HscTypes.HscEnv   -- The Environment corresponding ot the loaded modules 
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

findBindAnn :: 
  GhcMonad m => 
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule 
  -> m (Maybe CoreBndr)
findBindAnn annotation core = do
  let binds = CoreSyn.flattenBinds $ cm_binds core
  annbinds <- Monad.filterM (annotation . fst) binds
  let bndr = case annbinds of [] -> Nothing ; xs -> Just $ head $ fst (unzip annbinds)
  return bndr
  
findExprAnn :: 
  GhcMonad m => 
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule 
  -> m (Maybe CoreExpr)
findExprAnn annotation core = do
  let binds = CoreSyn.flattenBinds $ cm_binds core
  annbinds <- Monad.filterM (annotation . fst) binds
  let exprs = case annbinds of [] -> Nothing ; xs -> Just $ head $ snd (unzip annbinds)
  return exprs

hasCLasHAnnotation ::
  GhcMonad m =>
  (CLasHAnn -> Bool)
  -> Var.Var
  -> m Bool
hasCLasHAnnotation clashAnn var = do
  let deserializer = Serialized.deserializeWithData
  let target = Annotations.NamedTarget (Var.varName var)
  (anns :: [CLasHAnn]) <- GHC.findGlobalAnns deserializer target
  let top_ents = filter clashAnn anns
  case top_ents of
    [] -> return False
    xs -> return True

-- | Extracts the named binder from the given module.
findBind ::
  GhcMonad m =>
  String             -- ^ The Name of the Binder
  -> HscTypes.CoreModule   -- ^ The Module to look in
  -> m (Maybe CoreBndr) -- ^ The resulting binder
findBind name core = 
  case (findBinder (CoreSyn.flattenBinds $ cm_binds core)) name of
    Nothing -> return Nothing
    Just bndr -> return $ Just $ fst bndr

-- | Extracts the named expression from the given module.
findExpr ::
  GhcMonad m =>
  String             -- ^ The Name of the Binder
  -> HscTypes.CoreModule   -- ^ The Module to look in 
  -> m (Maybe CoreExpr) -- ^ The resulting expression
findExpr name core = 
  case (findBinder (CoreSyn.flattenBinds $ cm_binds core)) name of
    Nothing -> return Nothing
    Just bndr -> return $ Just $ snd bndr

-- | Extract a named bind from the given list of binds
findBinder :: [(CoreBndr, CoreExpr)] -> String -> Maybe (CoreBndr, CoreExpr)
findBinder binds lookfor =
  -- This ignores Recs and compares the name of the bind with lookfor,
  -- disregarding any namespaces in OccName and extra attributes in Name and
  -- Var.
  find (\(var, _) -> lookfor == (occNameString $ nameOccName $ getName var)) binds

-- vim: set ts=8 sw=2 sts=2 expandtab:
