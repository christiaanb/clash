{-# LANGUAGE ScopedTypeVariables #-}

module CLasH.Utils.GhcTools where
  
-- Standard modules
import qualified Monad
import qualified System.IO.Unsafe
import qualified Language.Haskell.TH as TH
import qualified Maybe

-- GHC API
import qualified Annotations
import qualified CoreSyn
import qualified CoreUtils
import qualified DynFlags
import qualified HscTypes
import qualified GHC
import qualified Name
import qualified Serialized
import qualified Var
import qualified Outputable
import Outputable(($+$), (<+>), nest, empty, text, vcat)
import qualified Class

-- Local Imports
import CLasH.Utils.Pretty
import CLasH.Translator.TranslatorTypes
import CLasH.Translator.Annotations
import CLasH.Utils

-- How far to indent the values after a Foo: header
align = 20
-- How far to indent all lines after the first
indent = 5

listBindings :: FilePath -> [FilePath] -> IO ()
listBindings libdir filenames = do
  (cores,_,_) <- loadModules libdir filenames Nothing
  let binds = concatMap (CoreSyn.flattenBinds . HscTypes.cm_binds) cores
  mapM listBinding binds
  putStr "\n=========================\n"
  let classes = concatMap (HscTypes.typeEnvClasses . HscTypes.cm_types) cores
  mapM listClass classes
  return ()

-- Slightly different version of hang, that always uses vcat instead of
-- sep, so the first line of d2 preserves its nesting.
hang' d1 n d2 = vcat [d1, nest n d2]

listBinding :: (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -> IO ()
listBinding (b, e) = putStr $ Outputable.showSDoc $
  (text "Binder:") <+> (text $ show b ++ "[" ++ show (Var.varUnique b) ++ "]")
  $+$ nest indent (
    hang' (text "Type of Binder:") align (Outputable.ppr $ Var.varType b)
    $+$ hang' (text "Expression:") align (text $ prettyShow e)
    $+$ nest align (Outputable.ppr e)
    $+$ hang' (text "Type of Expression:") align (Outputable.ppr $ CoreUtils.exprType e)
  )
  $+$ (text "\n") -- Add an empty line

listClass :: Class.Class -> IO ()
listClass c = putStr $ Outputable.showSDoc $
  (text "Class:") <+> (text $ show (Class.className c))
  $+$ nest indent (
    hang' (text "Selectors:") align (text $ show (Class.classSelIds c))
  )
  $+$ (text "\n") -- Add an empty line
  
-- | Show the core structure of the given binds in the given file.
listBind :: FilePath -> [FilePath] -> String -> IO ()
listBind libdir filenames name = do
  (cores,_,_) <- loadModules libdir filenames Nothing
  bindings <- concatM $ mapM (findBinder (hasVarName name)) cores
  mapM_ listBinding bindings
  return ()

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
  System.IO.Unsafe.unsafePerformIO $
      GHC.runGhc (Just libDir) $ do
        dflags <- GHC.getSessionDynFlags
        GHC.setSessionDynFlags dflags
        m
  
-- | Loads the given files and turns it into a core module
loadModules ::
  FilePath      -- ^ The GHC Library directory 
  -> [String]   -- ^ The files that need to be loaded
  -> Maybe Finder -- ^ What entities to build?
  -> IO ( [HscTypes.CoreModule]
        , HscTypes.HscEnv
        , [EntitySpec]
        ) -- ^ ( The loaded modules, the resulting ghc environment, the entities to build)
loadModules libdir filenames finder =
  GHC.defaultErrorHandler DynFlags.defaultDynFlags $
    GHC.runGhc (Just libdir) $ do
      dflags <- GHC.getSessionDynFlags
      GHC.setSessionDynFlags dflags
      cores <- mapM GHC.compileToCoreModule filenames
      env <- GHC.getSession
      specs <- case finder of
        Nothing -> return []
        Just f -> concatM $ mapM f cores
      return (cores, env, specs)

findBinds ::
  Monad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe [CoreSyn.CoreBndr])
findBinds criteria core = do
  binders <- findBinder criteria core
  case binders of
    [] -> return Nothing
    bndrs -> return $ Just $ map fst bndrs

findBind ::
  Monad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe CoreSyn.CoreBndr)
findBind criteria core = do
  binders <- findBinds criteria core
  case binders of
    Nothing -> return Nothing
    (Just bndrs) -> return $ Just $ head bndrs

findExprs ::
  Monad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe [CoreSyn.CoreExpr])
findExprs criteria core = do
  binders <- findBinder criteria core
  case binders of
    [] -> return Nothing
    bndrs -> return $ Just (map snd bndrs)

findExpr ::
  Monad m =>
  (Var.Var -> m Bool)
  -> HscTypes.CoreModule
  -> m (Maybe CoreSyn.CoreExpr)
findExpr criteria core = do
  exprs <- findExprs criteria core
  case exprs of
    Nothing -> return Nothing
    (Just exprs) -> return $ Just $ head exprs

findAnns ::
  Monad m =>
  (Var.Var -> m [CLasHAnn])
  -> HscTypes.CoreModule
  -> m [CLasHAnn]
findAnns criteria core = do
  let binds = CoreSyn.flattenBinds $ HscTypes.cm_binds core
  anns <- Monad.mapM (criteria . fst) binds
  case anns of
    [] -> return []
    xs -> return $ concat xs

-- | Find a binder in module according to a certain criteria
findBinder :: 
  Monad m =>
  (Var.Var -> m Bool)     -- ^ The criteria to filter the binders on
  -> HscTypes.CoreModule  -- ^ The module to be inspected
  -> m [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)] -- ^ The binders to meet the criteria
findBinder criteria core = do
  let binds = CoreSyn.flattenBinds $ HscTypes.cm_binds core
  Monad.filterM (criteria . fst) binds

-- | Determine if a binder has an Annotation meeting a certain criteria
isCLasHAnnotation ::
  GHC.GhcMonad m =>
  (CLasHAnn -> Bool)  -- ^ The criteria the Annotation has to meet
  -> Var.Var          -- ^ The Binder
  -> m [CLasHAnn]           -- ^ Indicates if binder has the Annotation
isCLasHAnnotation clashAnn var = do
  let deserializer = Serialized.deserializeWithData
  let target = Annotations.NamedTarget (Var.varName var)
  (anns :: [CLasHAnn]) <- GHC.findGlobalAnns deserializer target
  let annEnts = filter clashAnn anns
  return annEnts

-- | Determine if a binder has an Annotation meeting a certain criteria
hasCLasHAnnotation ::
  GHC.GhcMonad m =>
  (CLasHAnn -> Bool)  -- ^ The criteria the Annotation has to meet
  -> Var.Var          -- ^ The Binder
  -> m Bool           -- ^ Indicates if binder has the Annotation
hasCLasHAnnotation clashAnn var = do
  anns <- isCLasHAnnotation clashAnn var
  case anns of
    [] -> return False
    xs -> return True

-- | Determine if a binder has a certain name
hasVarName ::   
  Monad m =>
  String        -- ^ The name the binder has to have
  -> Var.Var    -- ^ The Binder
  -> m Bool     -- ^ Indicate if the binder has the name
hasVarName lookfor bind = return $ lookfor == Name.occNameString (Name.nameOccName $ Name.getName bind)


findInitStates ::
  (Var.Var -> GHC.Ghc Bool) -> 
  (Var.Var -> GHC.Ghc [CLasHAnn]) -> 
  HscTypes.CoreModule -> 
  GHC.Ghc (Maybe [(CoreSyn.CoreBndr, CoreSyn.CoreBndr)])
findInitStates statec annsc mod = do
  states <- findBinds statec mod
  anns  <- findAnns annsc mod
  let funs = Maybe.catMaybes (map extractInits anns)
  exprs' <- mapM (\x -> findBind (hasVarName (TH.nameBase x)) mod) funs
  let exprs = Maybe.catMaybes exprs'
  let inits = zipMWith (\a b -> (a,b)) states exprs
  return inits
  where
    extractInits :: CLasHAnn -> Maybe TH.Name
    extractInits (InitState x)  = Just x
    extractInits _              = Nothing
    zipMWith :: (a -> b -> c) -> (Maybe [a]) -> [b] -> (Maybe [c])
    zipMWith _ Nothing   _  = Nothing
    zipMWith f (Just as) bs = Just $ zipWith f as bs

-- | Make a complete spec out of a three conditions
findSpec ::
  (Var.Var -> GHC.Ghc Bool) -> (Var.Var -> GHC.Ghc Bool) -> (Var.Var -> GHC.Ghc [CLasHAnn]) -> (Var.Var -> GHC.Ghc Bool)
  -> Finder

findSpec topc statec annsc testc mod = do
  top <- findBind topc mod
  state <- findExprs statec mod
  anns <- findAnns annsc mod
  test <- findExpr testc mod
  inits <- findInitStates statec annsc mod
  return [(top, inits, test)]
  -- case top of
  --   Just t -> return [(t, state, test)]
  --   Nothing -> return error $ "Could not find top entity requested"
