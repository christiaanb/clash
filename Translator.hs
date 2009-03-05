module Translator where
import qualified Directory
import qualified List
import GHC hiding (loadModule, sigName)
import CoreSyn
import qualified CoreUtils
import qualified Var
import qualified Type
import qualified TyCon
import qualified DataCon
import qualified Maybe
import qualified Module
import qualified Control.Monad.State as State
import qualified Data.Foldable as Foldable
import Name
import qualified Data.Map as Map
import Data.Generics
import NameEnv ( lookupNameEnv )
import qualified HscTypes
import HscTypes ( cm_binds, cm_types )
import MonadUtils ( liftIO )
import Outputable ( showSDoc, ppr )
import GHC.Paths ( libdir )
import DynFlags ( defaultDynFlags )
import List ( find )
import qualified List
import qualified Monad

-- The following modules come from the ForSyDe project. They are really
-- internal modules, so ForSyDe.cabal has to be modified prior to installing
-- ForSyDe to get access to these modules.
import qualified ForSyDe.Backend.VHDL.AST as AST
import qualified ForSyDe.Backend.VHDL.Ppr
import qualified ForSyDe.Backend.VHDL.FileIO
import qualified ForSyDe.Backend.Ppr
-- This is needed for rendering the pretty printed VHDL
import Text.PrettyPrint.HughesPJ (render)

import TranslatorTypes
import HsValueMap
import Pretty
import Flatten
import FlattenTypes
import VHDLTypes
import qualified VHDL

main = do
  makeVHDL "Alu.hs" "register_bank" True

makeVHDL :: String -> String -> Bool -> IO ()
makeVHDL filename name stateful = do
  -- Load the module
  core <- loadModule filename
  -- Translate to VHDL
  vhdl <- moduleToVHDL core [(name, stateful)]
  -- Write VHDL to file
  let dir = "../vhdl/vhdl/" ++ name ++ "/"
  mapM (writeVHDL dir) vhdl
  return ()

-- | Show the core structure of the given binds in the given file.
listBind :: String -> String -> IO ()
listBind filename name = do
  core <- loadModule filename
  let binds = findBinds core [name]
  putStr "\n"
  putStr $ prettyShow binds
  putStr "\n\n"
  putStr $ showSDoc $ ppr binds
  putStr "\n\n"

-- | Translate the binds with the given names from the given core module to
--   VHDL. The Bool in the tuple makes the function stateful (True) or
--   stateless (False).
moduleToVHDL :: HscTypes.CoreModule -> [(String, Bool)] -> IO [AST.DesignFile]
moduleToVHDL core list = do
  let (names, statefuls) = unzip list
  --liftIO $ putStr $ prettyShow (cm_binds core)
  let binds = findBinds core names
  --putStr $ prettyShow binds
  -- Turn bind into VHDL
  let (vhdl, sess) = State.runState (mkVHDL binds statefuls) (VHDLSession core 0 Map.empty)
  mapM (putStr . render . ForSyDe.Backend.Ppr.ppr) vhdl
  putStr $ "\n\nFinal session:\n" ++ prettyShow sess ++ "\n\n"
  return vhdl

  where
    -- Turns the given bind into VHDL
    mkVHDL binds statefuls = do
      -- Add the builtin functions
      mapM addBuiltIn builtin_funcs
      -- Create entities and architectures for them
      Monad.zipWithM processBind statefuls binds
      modFuncs nameFlatFunction
      modFuncs VHDL.createEntity
      modFuncs VHDL.createArchitecture
      funcs <- getFuncs
      return $ VHDL.getDesignFiles (map snd funcs)

-- | Write the given design file to a file inside the given dir
--   The first library unit in the designfile must be an entity, whose name
--   will be used as a filename.
writeVHDL :: String -> AST.DesignFile -> IO ()
writeVHDL dir vhdl = do
  -- Create the dir if needed
  exists <- Directory.doesDirectoryExist dir
  Monad.unless exists $ Directory.createDirectory dir
  -- Find the filename
  let AST.DesignFile _ (u:us) = vhdl
  let AST.LUEntity (AST.EntityDec id _) = u
  let fname = dir ++ AST.fromVHDLId id ++ ".vhdl"
  -- Write the file
  ForSyDe.Backend.VHDL.FileIO.writeDesignFile vhdl fname

-- | Loads the given file and turns it into a core module.
loadModule :: String -> IO HscTypes.CoreModule
loadModule filename =
  defaultErrorHandler defaultDynFlags $ do
    runGhc (Just libdir) $ do
      dflags <- getSessionDynFlags
      setSessionDynFlags dflags
      --target <- guessTarget "adder.hs" Nothing
      --liftIO (print (showSDoc (ppr (target))))
      --liftIO $ printTarget target
      --setTargets [target]
      --load LoadAllTargets
      --core <- GHC.compileToCoreSimplified "Adders.hs"
      core <- GHC.compileToCoreSimplified filename
      return core

-- | Extracts the named binds from the given module.
findBinds :: HscTypes.CoreModule -> [String] -> [CoreBind]
findBinds core names = Maybe.mapMaybe (findBind (cm_binds core)) names

-- | Extract a named bind from the given list of binds
findBind :: [CoreBind] -> String -> Maybe CoreBind
findBind binds lookfor =
  -- This ignores Recs and compares the name of the bind with lookfor,
  -- disregarding any namespaces in OccName and extra attributes in Name and
  -- Var.
  find (\b -> case b of 
    Rec l -> False
    NonRec var _ -> lookfor == (occNameString $ nameOccName $ getName var)
  ) binds

-- | Processes the given bind as a top level bind.
processBind ::
  Bool                       -- ^ Should this be stateful function?
  -> CoreBind                -- ^ The bind to process
  -> VHDLState ()

processBind _ (Rec _) = error "Recursive binders not supported"
processBind stateful bind@(NonRec var expr) = do
  -- Create the function signature
  let ty = CoreUtils.exprType expr
  let hsfunc = mkHsFunction var ty stateful
  flattenBind hsfunc bind

-- | Flattens the given bind into the given signature and adds it to the
--   session. Then (recursively) finds any functions it uses and does the same
--   with them.
flattenBind ::
  HsFunction                         -- The signature to flatten into
  -> CoreBind                        -- The bind to flatten
  -> VHDLState ()

flattenBind _ (Rec _) = error "Recursive binders not supported"

flattenBind hsfunc bind@(NonRec var expr) = do
  -- Add the function to the session
  addFunc hsfunc
  -- Flatten the function
  let flatfunc = flattenFunction hsfunc bind
  -- Propagate state variables
  let flatfunc' = propagateState hsfunc flatfunc
  -- Store the flat function in the session
  setFlatFunc hsfunc flatfunc'
  -- Flatten any functions used
  let used_hsfuncs = Maybe.mapMaybe usedHsFunc (flat_defs flatfunc')
  State.mapM resolvFunc used_hsfuncs
  return ()

-- | Decide which incoming state variables will become state in the
--   given function, and which will be propagate to other applied
--   functions.
propagateState ::
  HsFunction
  -> FlatFunction
  -> FlatFunction

propagateState hsfunc flatfunc =
    flatfunc {flat_defs = apps', flat_sigs = sigs'} 
  where
    (olds, news) = unzip $ getStateSignals hsfunc flatfunc
    states' = zip olds news
    -- Find all signals used by all sigdefs
    uses = concatMap sigDefUses (flat_defs flatfunc)
    -- Find all signals that are used more than once (is there a
    -- prettier way to do this?)
    multiple_uses = uses List.\\ (List.nub uses)
    -- Find the states whose "old state" signal is used only once
    single_use_states = filter ((`notElem` multiple_uses) . fst) states'
    -- See if these single use states can be propagated
    (substate_sigss, apps') = unzip $ map (propagateState' single_use_states) (flat_defs flatfunc)
    substate_sigs = concat substate_sigss
    -- Mark any propagated state signals as SigSubState
    sigs' = map 
      (\(id, info) -> (id, if id `elem` substate_sigs then info {sigUse = SigSubState} else info))
      (flat_sigs flatfunc)

-- | Propagate the state into a single function application.
propagateState' ::
  [(SignalId, SignalId)]
                      -- ^ TODO
  -> SigDef           -- ^ The SigDef to process.
  -> ([SignalId], SigDef) 
                      -- ^ Any signal ids that should become substates,
                      --   and the resulting application.

propagateState' states def =
    if (is_FApp def) then
      (our_old ++ our_new, def {appFunc = hsfunc'})
    else
      ([], def)
  where
    hsfunc = appFunc def
    args = appArgs def
    res = appRes def
    our_states = filter our_state states
    -- A state signal belongs in this function if the old state is
    -- passed in, and the new state returned
    our_state (old, new) =
      any (old `Foldable.elem`) args
      && new `Foldable.elem` res
    (our_old, our_new) = unzip our_states
    -- Mark the result
    zipped_res = zipValueMaps res (hsFuncRes hsfunc)
    res' = fmap (mark_state (zip our_new [0..])) zipped_res
    -- Mark the args
    zipped_args = zipWith zipValueMaps args (hsFuncArgs hsfunc)
    args' = map (fmap (mark_state (zip our_old [0..]))) zipped_args
    hsfunc' = hsfunc {hsFuncArgs = args', hsFuncRes = res'}

    mark_state :: [(SignalId, StateId)] -> (SignalId, HsValueUse) -> HsValueUse
    mark_state states (id, use) =
      case lookup id states of
        Nothing -> use
        Just state_id -> State state_id

-- | Returns pairs of signals that should be mapped to state in this function.
getStateSignals ::
  HsFunction                      -- | The function to look at
  -> FlatFunction                 -- | The function to look at
  -> [(SignalId, SignalId)]   
        -- | TODO The state signals. The first is the state number, the second the
        --   signal to assign the current state to, the last is the signal
        --   that holds the new state.

getStateSignals hsfunc flatfunc =
  [(old_id, new_id) 
    | (old_num, old_id) <- args
    , (new_num, new_id) <- res
    , old_num == new_num]
  where
    sigs = flat_sigs flatfunc
    -- Translate args and res to lists of (statenum, sigid)
    args = concat $ zipWith stateList (hsFuncArgs hsfunc) (flat_args flatfunc)
    res = stateList (hsFuncRes hsfunc) (flat_res flatfunc)
    
-- | Find the given function, flatten it and add it to the session. Then
--   (recursively) do the same for any functions used.
resolvFunc ::
  HsFunction        -- | The function to look for
  -> VHDLState ()

resolvFunc hsfunc = do
  -- See if the function is already known
  func <- getFunc hsfunc
  case func of
    -- Already known, do nothing
    Just _ -> do
      return ()
    -- New function, resolve it
    Nothing -> do
      -- Get the current module
      core <- getModule
      -- Find the named function
      let bind = findBind (cm_binds core) name
      case bind of
        Nothing -> error $ "Couldn't find function " ++ name ++ " in current module."
        Just b  -> flattenBind hsfunc b
  where
    name = hsFuncName hsfunc

-- | Translate a top level function declaration to a HsFunction. i.e., which
--   interface will be provided by this function. This function essentially
--   defines the "calling convention" for hardware models.
mkHsFunction ::
  Var.Var         -- ^ The function defined
  -> Type         -- ^ The function type (including arguments!)
  -> Bool         -- ^ Is this a stateful function?
  -> HsFunction   -- ^ The resulting HsFunction

mkHsFunction f ty stateful=
  HsFunction hsname hsargs hsres
  where
    hsname  = getOccString f
    (arg_tys, res_ty) = Type.splitFunTys ty
    (hsargs, hsres) = 
      if stateful 
      then
        let
          -- The last argument must be state
          state_ty = last arg_tys
          state    = useAsState (mkHsValueMap state_ty)
          -- All but the last argument are inports
          inports = map (useAsPort . mkHsValueMap)(init arg_tys)
          hsargs   = inports ++ [state]
          hsres    = case splitTupleType res_ty of
            -- Result type must be a two tuple (state, ports)
            Just [outstate_ty, outport_ty] -> if Type.coreEqType state_ty outstate_ty
              then
                Tuple [state, useAsPort (mkHsValueMap outport_ty)]
              else
                error $ "Input state type of function " ++ hsname ++ ": " ++ (showSDoc $ ppr state_ty) ++ " does not match output state type: " ++ (showSDoc $ ppr outstate_ty)
            otherwise                -> error $ "Return type of top-level function " ++ hsname ++ " must be a two-tuple containing a state and output ports."
        in
          (hsargs, hsres)
      else
        -- Just use everything as a port
        (map (useAsPort . mkHsValueMap) arg_tys, useAsPort $ mkHsValueMap res_ty)

-- | Adds signal names to the given FlatFunction
nameFlatFunction ::
  HsFunction
  -> FuncData
  -> VHDLState ()

nameFlatFunction hsfunc fdata =
  let func = flatFunc fdata in
  case func of
    -- Skip (builtin) functions without a FlatFunction
    Nothing -> do return ()
    -- Name the signals in all other functions
    Just flatfunc ->
      let s = flat_sigs flatfunc in
      let s' = map nameSignal s in
      let flatfunc' = flatfunc { flat_sigs = s' } in
      setFlatFunc hsfunc flatfunc'
  where
    nameSignal :: (SignalId, SignalInfo) -> (SignalId, SignalInfo)
    nameSignal (id, info) =
      let hints = nameHints info in
      let parts = ("sig" : hints) ++ [show id] in
      let name = concat $ List.intersperse "_" parts in
      (id, info {sigName = Just name})

-- | Splits a tuple type into a list of element types, or Nothing if the type
--   is not a tuple type.
splitTupleType ::
  Type              -- ^ The type to split
  -> Maybe [Type]   -- ^ The tuples element types

splitTupleType ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) -> if TyCon.isTupleTyCon tycon 
      then
        Just args
      else
        Nothing
    Nothing -> Nothing

-- | A consise representation of a (set of) ports on a builtin function
type PortMap = HsValueMap (String, AST.TypeMark)
-- | A consise representation of a builtin function
data BuiltIn = BuiltIn String [PortMap] PortMap

-- | Map a port specification of a builtin function to a VHDL Signal to put in
--   a VHDLSignalMap
toVHDLSignalMap :: HsValueMap (String, AST.TypeMark) -> VHDLSignalMap
toVHDLSignalMap = fmap (\(name, ty) -> Just (VHDL.mkVHDLId name, ty))

-- | Translate a concise representation of a builtin function to something
--   that can be put into FuncMap directly.
addBuiltIn :: BuiltIn -> VHDLState ()
addBuiltIn (BuiltIn name args res) = do
    addFunc hsfunc
    setEntity hsfunc entity
  where
    hsfunc = HsFunction name (map useAsPort args) (useAsPort res)
    entity = Entity (VHDL.mkVHDLId name) (map toVHDLSignalMap args) (toVHDLSignalMap res) Nothing Nothing

builtin_funcs = 
  [ 
    BuiltIn "hwxor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwand" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwnot" [(Single ("a", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty))
  ]

-- vim: set ts=8 sw=2 sts=2 expandtab:
