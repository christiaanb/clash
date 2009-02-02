module Main(main) where
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
import qualified ForSyDe.Backend.Ppr
-- This is needed for rendering the pretty printed VHDL
import Text.PrettyPrint.HughesPJ (render)

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
          let binds = Maybe.mapMaybe (findBind (cm_binds core)) ["full_adder", "half_adder"]
          liftIO $ printBinds binds
          -- Turn bind into VHDL
          let vhdl = State.evalState (mkVHDL binds) (VHDLSession 0 [])
          liftIO $ putStr $ render $ ForSyDe.Backend.Ppr.ppr vhdl
          return ()
  where
    -- Turns the given bind into VHDL
    mkVHDL binds = do
      -- Add the builtin functions
      mapM (uncurry addFunc) builtin_funcs
      -- Get the function signatures
      funcs <- mapM mkHWFunction binds
      -- Add them to the session
      mapM (uncurry addFunc) funcs
      let entities = map getEntity (snd $ unzip funcs)
      -- Create architectures for them
      archs <- mapM getArchitecture binds
      return $ AST.DesignFile 
        []
        ((map AST.LUEntity entities) ++ (map AST.LUArch archs))

printTarget (Target (TargetFile file (Just x)) obj Nothing) =
  print $ show file

printBinds [] = putStr "done\n\n"
printBinds (b:bs) = do
  printBind b
  putStr "\n"
  printBinds bs

printBind (NonRec b expr) = do
  putStr "NonRec: "
  printBind' (b, expr)

printBind (Rec binds) = do
  putStr "Rec: \n"  
  foldl1 (>>) (map printBind' binds)

printBind' (b, expr) = do
  putStr $ getOccString b
  putStr $ showSDoc $ ppr expr
  putStr "\n"

findBind :: [CoreBind] -> String -> Maybe CoreBind
findBind binds lookfor =
  -- This ignores Recs and compares the name of the bind with lookfor,
  -- disregarding any namespaces in OccName and extra attributes in Name and
  -- Var.
  find (\b -> case b of 
    Rec l -> False
    NonRec var _ -> lookfor == (occNameString $ nameOccName $ getName var)
  ) binds

getPortMapEntry ::
  SignalNameMap  -- The port name to bind to
  -> SignalNameMap 
                            -- The signal or port to bind to it
  -> AST.AssocElem          -- The resulting port map entry
  
-- Accepts a port name and an argument to map to it.
-- Returns the appropriate line for in the port map
getPortMapEntry (Signal portname _) (Signal signame _) = 
  (Just portname) AST.:=>: (AST.ADName (AST.NSimple signame))

getInstantiations ::
  [SignalNameMap]   -- The arguments that need to be applied to the
                               -- expression.
  -> SignalNameMap  -- The output ports that the expression should generate.
  -> [(CoreBndr, SignalNameMap)] 
                               -- A list of bindings in effect
  -> CoreSyn.CoreExpr          -- The expression to generate an architecture for
  -> VHDLState ([AST.SigDec], [AST.ConcSm])    
                               -- The resulting VHDL code

-- A lambda expression binds the first argument (a) to the binder b.
getInstantiations (a:as) outs binds (Lam b expr) =
  getInstantiations as outs ((b, a):binds) expr

-- A case expression that checks a single variable and has a single
-- alternative, can be used to take tuples apart
getInstantiations args outs binds (Case (Var v) b _ [res]) =
  -- Split out the type of alternative constructor, the variables it binds
  -- and the expression to evaluate with the variables bound.
  let (altcon, bind_vars, expr) = res in
  case altcon of
    DataAlt datacon ->
      if (DataCon.isTupleCon datacon) then
        let 
          -- Lookup the scrutinee (which must be a variable bound to a tuple) in
          -- the existing bindings list and get the portname map for each of
          -- it's elements.
          Tuple tuple_ports = Maybe.fromMaybe 
            (error $ "Case expression uses unknown scrutinee " ++ getOccString v)
            (lookup v binds)
          -- Merge our existing binds with the new binds.
          binds' = (zip bind_vars tuple_ports) ++ binds 
        in
          -- Evaluate the expression with the new binds list
          getInstantiations args outs binds' expr
      else
        error "Data constructors other than tuples not supported"
    otherwise ->
      error "Case binders other than tuples not supported"

-- An application is an instantiation of a component
getInstantiations args outs binds app@(App expr arg) = do
  let ((Var f), fargs) = collectArgs app
      name = getOccString f
  if isTupleConstructor f 
    then do
      -- Get the signals we should bind our results to
      let Tuple outports = outs
      -- Split the tuple constructor arguments into types and actual values.
      let (_, vals) = splitTupleConstructorArgs fargs
      -- Bind each argument to each output signal
      res <- sequence $ zipWith 
        (\outs' expr' -> getInstantiations args outs' binds expr')
        outports vals
      -- res is a list of pairs of lists, so split out the signals and
      -- components into separate lists of lists
      let (sigs, comps) = unzip res
      -- And join all the signals and component instantiations together
      return $ (concat sigs, concat comps)
    else do
      -- This is an normal function application, which maps to a component
      -- instantiation.
      -- Lookup the hwfunction to instantiate
      HWFunction vhdl_id inports outport <- getHWFunc name
      -- Generate a unique name for the application
      appname <- uniqueName "app"
      -- Expand each argument to a signal or port name, possibly generating
      -- new signals and component instantiations
      (sigs, comps, args) <- expandArgs binds fargs
      -- Bind each of the input ports to the expanded signal or port
      let inmaps = zipWith getPortMapEntry inports args
      -- Bind each of the output ports to our output signals
      let outmaps = mapOutputPorts outport outs
      -- Build and return a component instantiation
      let comp = AST.CompInsSm
            (AST.unsafeVHDLBasicId appname)
            (AST.IUEntity (AST.NSimple vhdl_id))
            (AST.PMapAspect (inmaps ++ outmaps))
      return (sigs, (AST.CSISm comp) : comps)

getInstantiations args outs binds expr = 
  error $ "Unsupported expression" ++ (showSDoc $ ppr $ expr)

expandExpr ::
  [(CoreBndr, SignalNameMap)] 
                                         -- A list of bindings in effect
  -> CoreExpr                            -- The expression to expand
  -> VHDLState (
       [AST.SigDec],                     -- Needed signal declarations
       [AST.ConcSm],                     -- Needed component instantations and
                                         -- signal assignments.
       [SignalNameMap],       -- The signal names corresponding to
                                         -- the expression's arguments
       SignalNameMap)         -- The signal names corresponding to
                                         -- the expression's result.
expandExpr binds lam@(Lam b expr) = do
  -- Generate a new signal to which we will expect this argument to be bound.
  signal_name <- uniqueName ("arg_" ++ getOccString b)
  -- Find the type of the binder
  let (arg_ty, _) = Type.splitFunTy (CoreUtils.exprType lam)
  -- Create signal names for the binder
  let arg_signal = getPortNameMapForTy ("xxx") arg_ty
  -- Create the corresponding signal declarations
  let signal_decls = mkSignalsFromMap arg_signal
  -- Add the binder to the list of binds
  let binds' = (b, arg_signal) : binds
  -- Expand the rest of the expression
  (signal_decls', statements', arg_signals', res_signal') <- expandExpr binds' expr
  -- Properly merge the results
  return (signal_decls ++ signal_decls',
          statements',
          arg_signal : arg_signals',
          res_signal')

expandExpr binds (Var id) =
  return ([], [], [], Signal signal_id ty)
  where
    -- Lookup the id in our binds map
    Signal signal_id ty = Maybe.fromMaybe
      (error $ "Argument " ++ getOccString id ++ "is unknown")
      (lookup id binds)

expandExpr binds l@(Let (NonRec b bexpr) expr) = do
  (signal_decls, statements, arg_signals, res_signals) <- expandExpr binds bexpr
  let binds' = (b, res_signals) : binds
  (signal_decls', statements', arg_signals', res_signals') <- expandExpr binds' expr
  return (
    signal_decls ++ signal_decls',
    statements ++ statements',
    arg_signals',
    res_signals')

expandExpr binds app@(App _ _) = do
  let ((Var f), args) = collectArgs app
  if isTupleConstructor f 
    then
      expandBuildTupleExpr binds args
    else
      expandApplicationExpr binds (CoreUtils.exprType app) f args

expandExpr binds expr@(Case (Var v) b _ alts) =
  case alts of
    [alt] -> expandSingleAltCaseExpr binds v b alt
    otherwise -> error $ "Multiple alternative case expression not supported: " ++ (showSDoc $ ppr expr)

expandExpr binds expr@(Case _ b _ _) =
  error $ "Case expression with non-variable scrutinee not supported: " ++ (showSDoc $ ppr expr)

expandExpr binds expr = 
  error $ "Unsupported expression: " ++ (showSDoc $ ppr $ expr)

-- Expands the construction of a tuple into VHDL
expandBuildTupleExpr ::
  [(CoreBndr, SignalNameMap)] 
                                         -- A list of bindings in effect
  -> [CoreExpr]                          -- A list of expressions to put in the tuple
  -> VHDLState ( [AST.SigDec], [AST.ConcSm], [SignalNameMap], SignalNameMap)
                                         -- See expandExpr
expandBuildTupleExpr binds args = do
  -- Split the tuple constructor arguments into types and actual values.
  let (_, vals) = splitTupleConstructorArgs args
  -- Expand each of the values in the tuple
  (signals_declss, statementss, arg_signalss, res_signals) <-
    (Monad.liftM List.unzip4) $ mapM (expandExpr binds) vals
  if any (not . null) arg_signalss
    then error "Putting high order functions in tuples not supported"
    else
      return (
        concat signals_declss,
        concat statementss,
        [],
        Tuple res_signals)

-- Expands the most simple case expression that scrutinizes a plain variable
-- and has a single alternative. This simple form currently allows only for
-- unpacking tuple variables.
expandSingleAltCaseExpr ::
  [(CoreBndr, SignalNameMap)] 
                            -- A list of bindings in effect
  -> Var.Var                -- The scrutinee
  -> CoreBndr               -- The binder to bind the scrutinee to
  -> CoreAlt                -- The single alternative
  -> VHDLState ( [AST.SigDec], [AST.ConcSm], [SignalNameMap], SignalNameMap)
                                         -- See expandExpr

expandSingleAltCaseExpr binds v b alt@(DataAlt datacon, bind_vars, expr) =
  if not (DataCon.isTupleCon datacon) 
    then
      error $ "Dataconstructors other than tuple constructors not supported in case pattern of alternative: " ++ (showSDoc $ ppr alt)
    else
      let
        -- Lookup the scrutinee (which must be a variable bound to a tuple) in
        -- the existing bindings list and get the portname map for each of
        -- it's elements.
        Tuple tuple_ports = Maybe.fromMaybe 
          (error $ "Case expression uses unknown scrutinee " ++ getOccString v)
          (lookup v binds)
        -- TODO include b in the binds list
        -- Merge our existing binds with the new binds.
        binds' = (zip bind_vars tuple_ports) ++ binds 
      in
        -- Expand the expression with the new binds list
        expandExpr binds' expr

expandSingleAltCaseExpr _ _ _ alt =
  error $ "Case patterns other than data constructors not supported in case alternative: " ++ (showSDoc $ ppr alt)
      

-- Expands the application of argument to a function into VHDL
expandApplicationExpr ::
  [(CoreBndr, SignalNameMap)] 
                                         -- A list of bindings in effect
  -> Type                                -- The result type of the function call
  -> Var.Var                             -- The function to call
  -> [CoreExpr]                          -- A list of argumetns to apply to the function
  -> VHDLState ( [AST.SigDec], [AST.ConcSm], [SignalNameMap], SignalNameMap)
                                         -- See expandExpr
expandApplicationExpr binds ty f args = do
  let name = getOccString f
  -- Generate a unique name for the application
  appname <- uniqueName ("app_" ++ name)
  -- Lookup the hwfunction to instantiate
  HWFunction vhdl_id inports outport <- getHWFunc name
  -- Expand each of the args, so each of them is reduced to output signals
  (arg_signal_decls, arg_statements, arg_res_signals) <- expandArgs binds args
  -- Bind each of the input ports to the expanded arguments
  let inmaps = concat $ zipWith createAssocElems inports arg_res_signals
  -- Create signal names for our result
  let res_signal = getPortNameMapForTy (appname ++ "_out") ty
  -- Create the corresponding signal declarations
  let signal_decls = mkSignalsFromMap res_signal
  -- Bind each of the output ports to our output signals
  let outmaps = mapOutputPorts outport res_signal
  -- Instantiate the component
  let component = AST.CSISm $ AST.CompInsSm
        (AST.unsafeVHDLBasicId appname)
        (AST.IUEntity (AST.NSimple vhdl_id))
        (AST.PMapAspect (inmaps ++ outmaps))
  -- Merge the generated declarations
  return (
    signal_decls ++ arg_signal_decls,
    component : arg_statements,
    [], -- We don't take any extra arguments; we don't support higher order functions yet
    res_signal)
  
-- Creates a list of AssocElems (port map lines) that maps the given signals
-- to the given ports.
createAssocElems ::
  SignalNameMap      -- The port names to bind to
  -> SignalNameMap   -- The signals to bind to it
  -> [AST.AssocElem]            -- The resulting port map lines
  
createAssocElems (Signal port_id _) (Signal signal_id _) = 
  [(Just port_id) AST.:=>: (AST.ADName (AST.NSimple signal_id))]

createAssocElems (Tuple ports) (Tuple signals) = 
  concat $ zipWith createAssocElems ports signals

-- Generate a signal declaration for a signal with the given name and the
-- given type and no value. Also returns the id of the signal.
mkSignal :: String -> AST.TypeMark -> (AST.VHDLId, AST.SigDec)
mkSignal name ty =
  (id, mkSignalFromId id ty)
  where 
    id = AST.unsafeVHDLBasicId name

mkSignalFromId :: AST.VHDLId -> AST.TypeMark -> AST.SigDec
mkSignalFromId id ty =
  AST.SigDec id ty Nothing

-- Generates signal declarations for all the signals in the given map
mkSignalsFromMap ::
  SignalNameMap 
  -> [AST.SigDec]

mkSignalsFromMap (Signal id ty) =
  [mkSignalFromId id ty]

mkSignalsFromMap (Tuple signals) =
  concat $ map mkSignalsFromMap signals

expandArgs :: 
  [(CoreBndr, SignalNameMap)] -- A list of bindings in effect
  -> [CoreExpr]                          -- The arguments to expand
  -> VHDLState ([AST.SigDec], [AST.ConcSm], [SignalNameMap])  
                                         -- The resulting signal declarations,
                                         -- component instantiations and a
                                         -- VHDLName for each of the
                                         -- expressions passed in.
expandArgs binds (e:exprs) = do
  -- Expand the first expression
  (signal_decls, statements, arg_signals, res_signal) <- expandExpr binds e
  if not (null arg_signals)
    then error $ "Passing functions as arguments not supported: " ++ (showSDoc $ ppr e)
    else do
      (signal_decls', statements', res_signals') <- expandArgs binds exprs
      return (
        signal_decls ++ signal_decls',
        statements ++ statements',
        res_signal : res_signals')

expandArgs _ [] = return ([], [], [])

-- Is the given name a (binary) tuple constructor
isTupleConstructor :: Var.Var -> Bool
isTupleConstructor var =
  Name.isWiredInName name
  && Name.nameModule name == tuple_mod
  && (Name.occNameString $ Name.nameOccName name) == "(,)"
  where
    name = Var.varName var
    mod = nameModule name
    tuple_mod = Module.mkModule (Module.stringToPackageId "ghc-prim") (Module.mkModuleName "GHC.Tuple")

-- Split arguments into type arguments and value arguments This is probably
-- not really sufficient (not sure if Types can actually occur as value
-- arguments...)
splitTupleConstructorArgs :: [CoreExpr] -> ([CoreExpr], [CoreExpr])
splitTupleConstructorArgs (e:es) =
  case e of
    Type t     -> (e:tys, vals)
    otherwise  -> (tys, e:vals)
  where
    (tys, vals) = splitTupleConstructorArgs es

splitTupleConstructorArgs [] = ([], [])

mapOutputPorts ::
  SignalNameMap      -- The output portnames of the component
  -> SignalNameMap   -- The output portnames and/or signals to map these to
  -> [AST.AssocElem]            -- The resulting output ports

-- Map the output port of a component to the output port of the containing
-- entity.
mapOutputPorts (Signal portname _) (Signal signalname _) =
  [(Just portname) AST.:=>: (AST.ADName (AST.NSimple signalname))]

-- Map matching output ports in the tuple
mapOutputPorts (Tuple ports) (Tuple signals) =
  concat (zipWith mapOutputPorts ports signals)

getArchitecture ::
  CoreBind                  -- The binder to expand into an architecture
  -> VHDLState AST.ArchBody -- The resulting architecture
   
getArchitecture (Rec _) = error "Recursive binders not supported"

getArchitecture (NonRec var expr) = do
  let name = (getOccString var)
  HWFunction vhdl_id inports outport <- getHWFunc name
  sess <- State.get
  (signal_decls, statements, arg_signals, res_signal) <- expandExpr [] expr
  let inport_assigns = concat $ zipWith createSignalAssignments arg_signals inports
  let outport_assigns = createSignalAssignments outport res_signal
  return $ AST.ArchBody
    (AST.unsafeVHDLBasicId "structural")
    (AST.NSimple vhdl_id)
    (map AST.BDISD signal_decls)
    (inport_assigns ++ outport_assigns ++ statements)

-- Generate a VHDL entity declaration for the given function
getEntity :: HWFunction -> AST.EntityDec  
getEntity (HWFunction vhdl_id inports outport) = 
  AST.EntityDec vhdl_id ports
  where
    ports = 
      (concat $ map (mkIfaceSigDecs AST.In) inports)
      ++ mkIfaceSigDecs AST.Out outport

mkIfaceSigDecs ::
  AST.Mode                        -- The port's mode (In or Out)
  -> SignalNameMap        -- The ports to generate a map for
  -> [AST.IfaceSigDec]            -- The resulting ports
  
mkIfaceSigDecs mode (Signal port_id ty) =
  [AST.IfaceSigDec port_id mode ty]

mkIfaceSigDecs mode (Tuple ports) =
  concat $ map (mkIfaceSigDecs mode) ports

-- Create concurrent assignments of one map of signals to another. The maps
-- should have a similar form.
createSignalAssignments ::
  SignalNameMap         -- The signals to assign to
  -> SignalNameMap      -- The signals to assign
  -> [AST.ConcSm]                  -- The resulting assignments

-- A simple assignment of one signal to another (greatly complicated because
-- signal assignments can be conditional with multiple conditions in VHDL).
createSignalAssignments (Signal dst _) (Signal src _) =
    [AST.CSSASm assign]
  where
    src_name  = AST.NSimple src
    src_expr  = AST.PrimName src_name
    src_wform = AST.Wform [AST.WformElem src_expr Nothing]
    dst_name  = (AST.NSimple dst)
    assign    = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)

createSignalAssignments (Tuple dsts) (Tuple srcs) =
  concat $ zipWith createSignalAssignments dsts srcs

createSignalAssignments dst src =
  error $ "Non matching source and destination: " ++ show dst ++ "\nand\n" ++  show src

data SignalNameMap =
  Tuple [SignalNameMap]
  | Signal AST.VHDLId AST.TypeMark   -- A signal (or port) of the given (VDHL) type
  deriving (Show)

-- Generate a port name map (or multiple for tuple types) in the given direction for
-- each type given.
getPortNameMapForTys :: String -> Int -> [Type] -> [SignalNameMap]
getPortNameMapForTys prefix num [] = [] 
getPortNameMapForTys prefix num (t:ts) =
  (getPortNameMapForTy (prefix ++ show num) t) : getPortNameMapForTys prefix (num + 1) ts

getPortNameMapForTy :: String -> Type -> SignalNameMap
getPortNameMapForTy name ty =
  if (TyCon.isTupleTyCon tycon) then
    -- Expand tuples we find
    Tuple (getPortNameMapForTys name 0 args)
  else -- Assume it's a type constructor application, ie simple data type
    Signal (AST.unsafeVHDLBasicId name) (vhdl_ty ty)
  where
    (tycon, args) = Type.splitTyConApp ty 

data HWFunction = HWFunction { -- A function that is available in hardware
  vhdlId    :: AST.VHDLId,
  inPorts   :: [SignalNameMap],
  outPort   :: SignalNameMap
  --entity    :: AST.EntityDec
} deriving (Show)

-- Turns a CoreExpr describing a function into a description of its input and
-- output ports.
mkHWFunction ::
  CoreBind                                   -- The core binder to generate the interface for
  -> VHDLState (String, HWFunction)          -- The name of the function and its interface

mkHWFunction (NonRec var expr) =
    return (name, HWFunction (mkVHDLId name) inports outport)
  where
    name = getOccString var
    ty = CoreUtils.exprType expr
    (fargs, res) = Type.splitFunTys ty
    args = if length fargs == 1 then fargs else (init fargs)
    --state = if length fargs == 1 then () else (last fargs)
    inports = case args of
      -- Handle a single port specially, to prevent an extra 0 in the name
      [port] -> [getPortNameMapForTy "portin" port]
      ps     -> getPortNameMapForTys "portin" 0 ps
    outport = getPortNameMapForTy "portout" res

mkHWFunction (Rec _) =
  error "Recursive binders not supported"

data VHDLSession = VHDLSession {
  nameCount :: Int,                      -- A counter that can be used to generate unique names
  funcs     :: [(String, HWFunction)]    -- All functions available, indexed by name
} deriving (Show)

type VHDLState = State.State VHDLSession

-- Add the function to the session
addFunc :: String -> HWFunction -> VHDLState ()
addFunc name f = do
  fs <- State.gets funcs -- Get the funcs element from the session
  State.modify (\x -> x {funcs = (name, f) : fs }) -- Prepend name and f

-- Lookup the function with the given name in the current session. Errors if
-- it was not found.
getHWFunc :: String -> VHDLState HWFunction
getHWFunc name = do
  fs <- State.gets funcs -- Get the funcs element from the session
  return $ Maybe.fromMaybe
    (error $ "Function " ++ name ++ "is unknown? This should not happen!")
    (lookup name fs)

-- Makes the given name unique by appending a unique number.
-- This does not do any checking against existing names, so it only guarantees
-- uniqueness with other names generated by uniqueName.
uniqueName :: String -> VHDLState String
uniqueName name = do
  count <- State.gets nameCount -- Get the funcs element from the session
  State.modify (\s -> s {nameCount = count + 1})
  return $ name ++ "_" ++ (show count)

-- Shortcut
mkVHDLId :: String -> AST.VHDLId
mkVHDLId = AST.unsafeVHDLBasicId

builtin_funcs = 
  [ 
    ("hwxor", HWFunction (mkVHDLId "hwxor") [Signal (mkVHDLId "a") vhdl_bit_ty, Signal (mkVHDLId "b") vhdl_bit_ty] (Signal (mkVHDLId "o") vhdl_bit_ty)),
    ("hwand", HWFunction (mkVHDLId "hwand") [Signal (mkVHDLId "a") vhdl_bit_ty, Signal (mkVHDLId "b") vhdl_bit_ty] (Signal (mkVHDLId "o") vhdl_bit_ty)),
    ("hwor", HWFunction (mkVHDLId "hwor") [Signal (mkVHDLId "a") vhdl_bit_ty, Signal (mkVHDLId "b") vhdl_bit_ty] (Signal (mkVHDLId "o") vhdl_bit_ty)),
    ("hwnot", HWFunction (mkVHDLId "hwnot") [Signal (mkVHDLId "i") vhdl_bit_ty] (Signal (mkVHDLId "o") vhdl_bit_ty))
  ]

vhdl_bit_ty :: AST.TypeMark
vhdl_bit_ty = AST.unsafeVHDLBasicId "Bit"

-- Translate a Haskell type to a VHDL type
vhdl_ty :: Type -> AST.TypeMark
vhdl_ty ty = Maybe.fromMaybe
  (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
  (vhdl_ty_maybe ty)

-- Translate a Haskell type to a VHDL type
vhdl_ty_maybe :: Type -> Maybe AST.TypeMark
vhdl_ty_maybe ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) ->
      let name = TyCon.tyConName tycon in
        -- TODO: Do something more robust than string matching
        case getOccString name of
          "Bit"      -> Just vhdl_bit_ty
          otherwise  -> Nothing
    otherwise -> Nothing

-- vim: set ts=8 sw=2 sts=2 expandtab:
