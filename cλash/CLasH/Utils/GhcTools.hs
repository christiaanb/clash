{-# LANGUAGE ScopedTypeVariables #-}

module CLasH.Utils.GhcTools where
  
-- Standard modules
import qualified Monad
import qualified System.IO.Unsafe

-- GHC API
import qualified Annotations
import qualified CoreSyn
import qualified DynFlags
import qualified HscTypes
import qualified GHC
import qualified Name
import qualified Serialized
import qualified Var

-- Local Imports
import CLasH.Translator.Annotations

-- Change a DynFlag from within the Ghc monad. Strangely enough there seems to
-- be no standard function to do exactly this.
setDynFlag :: DynFlags.DynFlag -> GHC.Ghc ()
setDynFlag dflag = do
  dflags <- GHC.getSessionDynFlags
  let dflags' = DynFlags.dopt_set dflags dflag
  GHC.setSessionDynFlags dflags'
  return ()

-- We don't want the IO monad sprinkled around everywhere, so we hide it.
-- This should be safe as long as we only do simple things in the GhcMonad
-- such as interface lookups and evaluating simple expressions that
-- don't have side effects themselves (Or rather, that don't use
-- unsafePerformIO themselves, since normal side effectful function would
-- just return an IO monad when they are evaluated).
unsafeRunGhc :: FilePath -> GHC.Ghc a -> a
unsafeRunGhc libDir m =
  System.IO.Unsafe.unsafePerformIO $ do
      GHC.runGhc (Just libDir) $ do
        dflags <- GHC.getSessionDynFlags
        GHC.setSessionDynFlags dflags
        m
  
-- | Loads the given files and turns it into a core module
loadModules ::
  FilePath      -- ^ The GHC Library directory 
  -> [String]   -- ^ The files that need to be loaded
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreBndr)) -- ^ The TopEntity finder
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreBndr)) -- ^ The InitState finder
  -> (HscTypes.CoreModule -> GHC.Ghc (Maybe CoreSyn.CoreExpr)) -- ^ The TestInput finder
  -> IO ( [HscTypes.CoreModule]
        , [Maybe CoreSyn.CoreBndr]
        , [Maybe CoreSyn.CoreBndr]
        , [Maybe CoreSyn.CoreExpr]
        , HscTypes.HscEnv
        ) -- ^ ( The loaded modules, the TopEntity, the InitState, the TestInput
          --   , The Environment corresponding of the loaded modules
          --   )
loadModules libdir filenames topEntLoc initSLoc testLoc =
  GHC.defaultErrorHandler DynFlags.defaultDynFlags $ do
    GHC.runGhc (Just libdir) $ do
      dflags <- GHC.getSessionDynFlags
      GHC.setSessionDynFlags dflags
      cores <- mapM GHC.compileToCoreModule filenames
      env <- GHC.getSession
      top_entity <- mapM topEntLoc cores
      init_state <- mapM initSLoc cores
      test_input <- mapM testLoc cores
      return (cores, top_entity, init_state, test_input, env)

findBind ::
  GHC.GhcMonad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe CoreSyn.CoreBndr)
findBind criteria core = do
  binders <- findBinder criteria core
  case binders of
    [] -> return Nothing
    bndrs -> return $ Just $ fst $ head bndrs

findExpr ::
  GHC.GhcMonad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe CoreSyn.CoreExpr)
findExpr criteria core = do
  binders <- findBinder criteria core
  case binders of
    [] -> return Nothing
    bndrs -> return $ Just $ snd $ head bndrs

-- | Find a binder in module according to a certain criteria
findBinder :: 
  GHC.GhcMonad m =>
  (Var.Var -> m Bool)     -- ^ The criteria to filter the binders on
  -> HscTypes.CoreModule  -- ^ The module to be inspected
  -> m [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ The binders to meet the criteria
findBinder criteria core = do
  let binds = CoreSyn.flattenBinds $ HscTypes.cm_binds core
  critbinds <- Monad.filterM (criteria . fst) binds
  return critbinds

-- | Determine if a binder has an Annotation meeting a certain criteria
hasCLasHAnnotation ::
  GHC.GhcMonad m =>
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
  GHC.GhcMonad m =>
  String        -- ^ The name the binder has to have
  -> Var.Var    -- ^ The Binder
  -> m Bool     -- ^ Indicate if the binder has the name
hasVarName lookfor bind = return $ lookfor == (Name.occNameString $ Name.nameOccName $ Name.getName bind)
