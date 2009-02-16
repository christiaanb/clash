module Translator where
import GHC
import CoreSyn
import qualified CoreUtils
import qualified Var
import qualified Type
import qualified TyCon
import qualified DataCon
import qualified Maybe
import qualified Module
import qualified Control.Monad.State as State
import Name
import qualified Data.Map as Map
import Data.Generics
import NameEnv ( lookupNameEnv )
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

main = 
    do
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
          core <- GHC.compileToCoreSimplified "Adders.hs"
          --liftIO $ printBinds (cm_binds core)
          let binds = Maybe.mapMaybe (findBind (cm_binds core)) ["sfull_adder"]
          liftIO $ putStr $ prettyShow binds
          -- Turn bind into VHDL
          let (vhdl, sess) = State.runState (mkVHDL binds) (VHDLSession core 0 Map.empty)
          liftIO $ putStr $ render $ ForSyDe.Backend.Ppr.ppr vhdl
          liftIO $ ForSyDe.Backend.VHDL.FileIO.writeDesignFile vhdl "../vhdl/vhdl/output.vhdl"
          liftIO $ putStr $ "\n\nFinal session:\n" ++ prettyShow sess ++ "\n\n"
          return ()
  where
    -- Turns the given bind into VHDL
    mkVHDL binds = do
      -- Add the builtin functions
      mapM addBuiltIn builtin_funcs
      -- Create entities and architectures for them
      mapM processBind binds
      modFuncs nameFlatFunction
      modFuncs VHDL.createEntity
      modFuncs VHDL.createArchitecture
      -- Extract the library units generated from all the functions in the
      -- session.
      funcs <- getFuncs
      let units = concat $ map VHDL.getLibraryUnits funcs
      return $ AST.DesignFile 
        []
        units

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
  CoreBind                        -- The bind to process
  -> VHDLState ()

processBind  (Rec _) = error "Recursive binders not supported"
processBind bind@(NonRec var expr) = do
  -- Create the function signature
  let ty = CoreUtils.exprType expr
  let hsfunc = mkHsFunction var ty
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
  -- Flatten the function
  let flatfunc = flattenFunction hsfunc bind
  addFunc hsfunc
  setFlatFunc hsfunc flatfunc
  let used_hsfuncs = map appFunc (flat_apps flatfunc)
  State.mapM resolvFunc used_hsfuncs
  return ()

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
  -> HsFunction   -- ^ The resulting HsFunction

mkHsFunction f ty =
  HsFunction hsname hsargs hsres
  where
    hsname  = getOccString f
    (arg_tys, res_ty) = Type.splitFunTys ty
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
      let s' = map (\(id, (SignalInfo Nothing ty)) -> (id, SignalInfo (Just $ "sig_" ++ (show id)) ty)) s in
      let flatfunc' = flatfunc { flat_sigs = s' } in
      setFlatFunc hsfunc flatfunc'

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
toVHDLSignalMap = fmap (\(name, ty) -> (VHDL.mkVHDLId name, ty))

-- | Translate a concise representation of a builtin function to something
--   that can be put into FuncMap directly.
addBuiltIn :: BuiltIn -> VHDLState ()
addBuiltIn (BuiltIn name args res) = do
    addFunc hsfunc
    setEntity hsfunc entity
  where
    hsfunc = HsFunction name (map useAsPort args) (useAsPort res)
    entity = Entity (VHDL.mkVHDLId name) (map toVHDLSignalMap args) (toVHDLSignalMap res) Nothing

builtin_funcs = 
  [ 
    BuiltIn "hwxor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwand" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwnot" [(Single ("a", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty))
  ]

-- vim: set ts=8 sw=2 sts=2 expandtab:
