--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

-- Standard modules
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Maybe
import qualified Control.Monad as Monad
import qualified Control.Arrow as Arrow
import qualified Control.Monad.Trans.State as State
import qualified Data.Traversable as Traversable
import qualified Data.Monoid as Monoid
import Data.Accessor
import qualified Data.Accessor.MonadState as MonadState
import Text.Regex.Posix
import Debug.Trace

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import CoreSyn
import qualified Type
import qualified Name
import qualified OccName
import qualified Var
import qualified Id
import qualified IdInfo
import qualified TyCon
import qualified DataCon
import qualified CoreSubst
import Outputable ( showSDoc, ppr )

-- Local imports
import VHDLTypes
import Flatten
import FlattenTypes
import TranslatorTypes
import HsValueMap
import Pretty
import CoreTools
import Constants
import Generate
import GlobalNameTable

createDesignFiles ::
  [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
  -> [(AST.VHDLId, AST.DesignFile)]

createDesignFiles binds =
  (mkVHDLBasicId "types", AST.DesignFile ieee_context [type_package]) :
  map (Arrow.second $ AST.DesignFile full_context) units
  
  where
    init_session = VHDLSession Map.empty Map.empty builtin_funcs globalNameTable
    (units, final_session) = 
      State.runState (createLibraryUnits binds) init_session
    ty_decls = map (uncurry AST.TypeDec) $ Map.elems (final_session ^. vsTypes)
    ieee_context = [
        AST.Library $ mkVHDLBasicId "IEEE",
        mkUseAll ["IEEE", "std_logic_1164"],
        mkUseAll ["IEEE", "numeric_std"]
      ]
    full_context =
      mkUseAll ["work", "types"]
      : ieee_context
    type_package = AST.LUPackageDec $ AST.PackageDec (mkVHDLBasicId "types") (map AST.PDITD ty_decls)

-- Create a use foo.bar.all statement. Takes a list of components in the used
-- name. Must contain at least two components
mkUseAll :: [String] -> AST.ContextItem
mkUseAll ss = 
  AST.Use $ from AST.:.: AST.All
  where
    base_prefix = (AST.NSimple $ mkVHDLBasicId $ head ss)
    from = foldl select base_prefix (tail ss)
    select prefix s = AST.NSelected $ prefix AST.:.: (AST.SSimple $ mkVHDLBasicId s)
      
createLibraryUnits ::
  [(CoreSyn.CoreBndr, CoreSyn.CoreExpr)]
  -> VHDLState [(AST.VHDLId, [AST.LibraryUnit])]

createLibraryUnits binds = do
  entities <- Monad.mapM createEntity binds
  archs <- Monad.mapM createArchitecture binds
  return $ zipWith 
    (\ent arch -> 
      let AST.EntityDec id _ = ent in 
      (id, [AST.LUEntity ent, AST.LUArch arch])
    )
    entities archs

-- | Create an entity for a given function
createEntity ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- | The function
  -> VHDLState AST.EntityDec -- | The resulting entity

createEntity (fname, expr) = do
      -- Strip off lambda's, these will be arguments
      let (args, letexpr) = CoreSyn.collectBinders expr
      args' <- Monad.mapM mkMap args
      -- There must be a let at top level 
      let (CoreSyn.Let binds (CoreSyn.Var res)) = letexpr
      res' <- mkMap res
      let ent_decl' = createEntityAST fname args' res'
      let AST.EntityDec entity_id _ = ent_decl' 
      let signature = Entity entity_id args' res'
      modA vsSignatures (Map.insert (bndrToString fname) signature)
      return ent_decl'
  where
    mkMap :: 
      --[(SignalId, SignalInfo)] 
      CoreSyn.CoreBndr 
      -> VHDLState VHDLSignalMapElement
    -- We only need the vsTypes element from the state
    mkMap = (\bndr ->
      let
        --info = Maybe.fromMaybe
        --  (error $ "Signal not found in the name map? This should not happen!")
        --  (lookup id sigmap)
        --  Assume the bndr has a valid VHDL id already
        id = bndrToVHDLId bndr
        ty = Var.varType bndr
      in
        if True -- isPortSigUse $ sigUse info
          then do
            type_mark <- vhdl_ty ty
            return $ Just (id, type_mark)
          else
            return $ Nothing
       )

  -- | Create the VHDL AST for an entity
createEntityAST ::
  CoreSyn.CoreBndr             -- | The name of the function
  -> [VHDLSignalMapElement]    -- | The entity's arguments
  -> VHDLSignalMapElement      -- | The entity's result
  -> AST.EntityDec             -- | The entity with the ent_decl filled in as well

createEntityAST name args res =
  AST.EntityDec vhdl_id ports
  where
    -- Create a basic Id, since VHDL doesn't grok filenames with extended Ids.
    vhdl_id = mkVHDLBasicId $ bndrToString name
    ports = Maybe.catMaybes $ 
              map (mkIfaceSigDec AST.In) args
              ++ [mkIfaceSigDec AST.Out res]
              ++ [clk_port]
    -- Add a clk port if we have state
    clk_port = if True -- hasState hsfunc
      then
        Just $ AST.IfaceSigDec (mkVHDLExtId "clk") AST.In VHDL.std_logic_ty
      else
        Nothing

-- | Create a port declaration
mkIfaceSigDec ::
  AST.Mode                         -- | The mode for the port (In / Out)
  -> Maybe (AST.VHDLId, AST.TypeMark)    -- | The id and type for the port
  -> Maybe AST.IfaceSigDec               -- | The resulting port declaration

mkIfaceSigDec mode (Just (id, ty)) = Just $ AST.IfaceSigDec id mode ty
mkIfaceSigDec _ Nothing = Nothing

-- | Generate a VHDL entity name for the given hsfunc
mkEntityId hsfunc =
  -- TODO: This doesn't work for functions with multiple signatures!
  -- Use a Basic Id, since using extended id's for entities throws off
  -- precision and causes problems when generating filenames.
  mkVHDLBasicId $ hsFuncName hsfunc

-- | Create an architecture for a given function
createArchitecture ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The function
  -> VHDLState AST.ArchBody -- ^ The architecture for this function

createArchitecture (fname, expr) = do
  --signaturemap <- getA vsSignatures
  --let signature = Maybe.fromMaybe 
  --      (error $ "Generating architecture for function " ++ (prettyShow hsfunc) ++ "without signature? This should not happen!")
  --      (Map.lookup hsfunc signaturemap)
  let entity_id = mkVHDLBasicId $ bndrToString fname
  -- Strip off lambda's, these will be arguments
  let (args, letexpr) = CoreSyn.collectBinders expr
  -- There must be a let at top level 
  let (CoreSyn.Let (CoreSyn.Rec binds) res) = letexpr

  -- Create signal declarations for all internal and state signals
  sig_dec_maybes <- mapM (mkSigDec' . fst) binds
  let sig_decs = Maybe.catMaybes $ sig_dec_maybes

  statements <- Monad.mapM mkConcSm binds
  return $ AST.ArchBody (mkVHDLBasicId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) (statements ++ procs')
  where
    procs = map mkStateProcSm [] -- (makeStatePairs flatfunc)
    procs' = map AST.CSPSm procs
    -- mkSigDec only uses vsTypes from the state
    mkSigDec' = mkSigDec

-- | Looks up all pairs of old state, new state signals, together with
--   the state id they represent.
makeStatePairs :: FlatFunction -> [(StateId, SignalInfo, SignalInfo)]
makeStatePairs flatfunc =
  [(Maybe.fromJust $ oldStateId $ sigUse old_info, old_info, new_info) 
    | old_info <- map snd (flat_sigs flatfunc)
    , new_info <- map snd (flat_sigs flatfunc)
	-- old_info must be an old state (and, because of the next equality,
	-- new_info must be a new state).
	, Maybe.isJust $ oldStateId $ sigUse old_info
	-- And the state numbers must match
    , (oldStateId $ sigUse old_info) == (newStateId $ sigUse new_info)]

    -- Replace the second tuple element with the corresponding SignalInfo
    --args_states = map (Arrow.second $ signalInfo sigs) args
mkStateProcSm :: (StateId, SignalInfo, SignalInfo) -> AST.ProcSm
mkStateProcSm (num, old, new) =
  AST.ProcSm label [clk] [statement]
  where
    label       = mkVHDLExtId $ "state_" ++ (show num)
    clk         = mkVHDLExtId "clk"
    rising_edge = AST.NSimple $ mkVHDLBasicId "rising_edge"
    wform       = AST.Wform [AST.WformElem (AST.PrimName $ AST.NSimple $ getSignalId new) Nothing]
    assign      = AST.SigAssign (AST.NSimple $ getSignalId old) wform
    rising_edge_clk = AST.PrimFCall $ AST.FCall rising_edge [Nothing AST.:=>: (AST.ADName $ AST.NSimple clk)]
    statement   = AST.IfSm rising_edge_clk [assign] [] Nothing

mkSigDec :: CoreSyn.CoreBndr -> VHDLState (Maybe AST.SigDec)
mkSigDec bndr =
  if True then do --isInternalSigUse use || isStateSigUse use then do
    type_mark <- vhdl_ty $ Var.varType bndr
    return $ Just (AST.SigDec (bndrToVHDLId bndr) type_mark Nothing)
  else
    return Nothing

-- | Creates a VHDL Id from a named SignalInfo. Errors out if the SignalInfo
--   is not named.
getSignalId :: SignalInfo -> AST.VHDLId
getSignalId info =
    mkVHDLExtId $ Maybe.fromMaybe
      (error $ "Unnamed signal? This should not happen!")
      (sigName info)

-- | Transforms a core binding into a VHDL concurrent statement
mkConcSm ::
  (CoreSyn.CoreBndr, CoreSyn.CoreExpr) -- ^ The binding to process
  -> VHDLState AST.ConcSm  -- ^ The corresponding VHDL component instantiation.

mkConcSm (bndr, app@(CoreSyn.App _ _))= do
  let (CoreSyn.Var f, args) = CoreSyn.collectArgs app
  case Var.globalIdVarDetails f of
    IdInfo.VanillaGlobal -> do
      -- It's a global value imported from elsewhere. These can be builting
      -- functions.
      funSignatures <- getA vsNameTable
      case (Map.lookup (bndrToString f) funSignatures) of
        Just funSignature ->
          let
            sigs = map (bndrToString.varBndr) args
            sigsNames = map (\signal -> (AST.PrimName (AST.NSimple (mkVHDLExtId signal)))) sigs
            func = (snd funSignature) sigsNames
            src_wform = AST.Wform [AST.WformElem func Nothing]
            dst_name = AST.NSimple (mkVHDLExtId (bndrToString bndr))
            assign = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)
          in
            return $ AST.CSSASm assign
        Nothing -> error $ "Using function from another module that is not a known builtin: " ++ pprString f
    IdInfo.NotGlobalId -> do
      signatures <- getA vsSignatures
      -- This is a local id, so it should be a function whose definition we
      -- have and which can be turned into a component instantiation.
      let  
        signature = Maybe.fromMaybe 
          (error $ "Using function '" ++ (bndrToString f) ++ "' without signature? This should not happen!") 
          (Map.lookup (bndrToString f) signatures)
        entity_id = ent_id signature
        label = bndrToString bndr
        -- Add a clk port if we have state
        --clk_port = Maybe.fromJust $ mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
        --portmaps = mkAssocElems sigs args res signature ++ (if hasState hsfunc then [clk_port] else [])
        portmaps = mkAssocElems args bndr signature
        in
          return $ AST.CSISm $ AST.CompInsSm (mkVHDLExtId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect portmaps)
    details -> error $ "Calling unsupported function " ++ pprString f ++ " with GlobalIdDetails " ++ pprString details

-- GHC generates some funny "r = r" bindings in let statements before
-- simplification. This outputs some dummy ConcSM for these, so things will at
-- least compile for now.
mkConcSm (bndr, CoreSyn.Var _) = return $ AST.CSPSm $ AST.ProcSm (mkVHDLBasicId "unused") [] []

-- A single alt case must be a selector. This means thee scrutinee is a simple
-- variable, the alternative is a dataalt with a single non-wild binder that
-- is also returned.
mkConcSm (bndr, expr@(Case (Var scrut) b ty [alt])) =
  case alt of
    (DataAlt dc, bndrs, (Var sel_bndr)) -> do
      case List.elemIndex sel_bndr bndrs of
        Just i -> do
          labels <- getFieldLabels (Id.idType scrut)
          let label = labels!!i
          let sel_name = mkSelectedName scrut label
          let sel_expr = AST.PrimName sel_name
          return $ mkUncondAssign (Left bndr) sel_expr
        Nothing -> error $ "VHDL.mkConcSM Not in normal form: Not a selector case:\n" ++ (pprString expr)
      
    _ -> error $ "VHDL.mkConcSM Not in normal form: Not a selector case:\n" ++ (pprString expr)

-- Multiple case alt are be conditional assignments and have only wild
-- binders in the alts and only variables in the case values and a variable
-- for a scrutinee. We check the constructor of the second alt, since the
-- first is the default case, if there is any.
mkConcSm (bndr, (Case (Var scrut) b ty [(_, _, Var false), (con, _, Var true)])) =
  let
    cond_expr = (varToVHDLExpr scrut) AST.:=: (conToVHDLExpr con)
    true_expr  = (varToVHDLExpr true)
    false_expr  = (varToVHDLExpr false)
  in
    return $ mkCondAssign (Left bndr) cond_expr true_expr false_expr
mkConcSm (_, (Case (Var _) _ _ alts)) = error "VHDL.mkConcSm Not in normal form: Case statement with more than two alternatives"
mkConcSm (_, Case _ _ _ _) = error "VHDL.mkConcSm Not in normal form: Case statement has does not have a simple variable as scrutinee"

-- Create an unconditional assignment statement
mkUncondAssign ::
  Either CoreBndr AST.VHDLName -- ^ The signal to assign to
  -> AST.Expr -- ^ The expression to assign
  -> AST.ConcSm -- ^ The resulting concurrent statement
mkUncondAssign dst expr = mkAssign dst Nothing expr

-- Create a conditional assignment statement
mkCondAssign ::
  Either CoreBndr AST.VHDLName -- ^ The signal to assign to
  -> AST.Expr -- ^ The condition
  -> AST.Expr -- ^ The value when true
  -> AST.Expr -- ^ The value when false
  -> AST.ConcSm -- ^ The resulting concurrent statement
mkCondAssign dst cond true false = mkAssign dst (Just (cond, true)) false

-- Create a conditional or unconditional assignment statement
mkAssign ::
  Either CoreBndr AST.VHDLName -> -- ^ The signal to assign to
  Maybe (AST.Expr , AST.Expr) -> -- ^ Optionally, the condition to test for
                                 -- and the value to assign when true.
  AST.Expr -> -- ^ The value to assign when false or no condition
  AST.ConcSm -- ^ The resulting concurrent statement

mkAssign dst cond false_expr =
  let
    -- I'm not 100% how this assignment AST works, but this gets us what we
    -- want...
    whenelse = case cond of
      Just (cond_expr, true_expr) -> 
        let 
          true_wform = AST.Wform [AST.WformElem true_expr Nothing] 
        in
          [AST.WhenElse true_wform cond_expr]
      Nothing -> []
    false_wform = AST.Wform [AST.WformElem false_expr Nothing]
    dst_name  = case dst of
      Left bndr -> AST.NSimple (bndrToVHDLId bndr)
      Right name -> name
    assign    = dst_name AST.:<==: (AST.ConWforms whenelse false_wform Nothing)
  in
    AST.CSSASm assign

-- Create a record field selector that selects the given label from the record
-- stored in the given binder.
mkSelectedName :: CoreBndr -> AST.VHDLId -> AST.VHDLName
mkSelectedName bndr label =
  let 
    sel_prefix = AST.NSimple $ bndrToVHDLId bndr
    sel_suffix = AST.SSimple $ label
  in
    AST.NSelected $ sel_prefix AST.:.: sel_suffix 

-- Finds the field labels for VHDL type generated for the given Core type,
-- which must result in a record type.
getFieldLabels :: Type.Type -> VHDLState [AST.VHDLId]
getFieldLabels ty = do
  -- Ensure that the type is generated (but throw away it's VHDLId)
  vhdl_ty ty
  -- Get the types map, lookup and unpack the VHDL TypeDef
  types <- getA vsTypes
  case Map.lookup (OrdType ty) types of
    Just (_, AST.TDR (AST.RecordTypeDef elems)) -> return $ map (\(AST.ElementDec id _) -> id) elems
    _ -> error $ "VHDL.getFieldLabels Type not found or not a record type? This should not happen! Type: " ++ (show ty)

-- Turn a variable reference into a AST expression
varToVHDLExpr :: Var.Var -> AST.Expr
varToVHDLExpr var = AST.PrimName $ AST.NSimple $ bndrToVHDLId var

-- Turn a constructor into an AST expression. For dataconstructors, this is
-- only the constructor itself, not any arguments it has. Should not be called
-- with a DEFAULT constructor.
conToVHDLExpr :: CoreSyn.AltCon -> AST.Expr
conToVHDLExpr (DataAlt dc) = AST.PrimLit lit
  where
    tycon = DataCon.dataConTyCon dc
    tyname = TyCon.tyConName tycon
    dcname = DataCon.dataConName dc
    lit = case Name.getOccString tyname of
      -- TODO: Do something more robust than string matching
      "Bit"      -> case Name.getOccString dcname of "High" -> "'1'"; "Low" -> "'0'"
      "Bool" -> case Name.getOccString dcname of "True" -> "true"; "False" -> "false"
conToVHDLExpr (LitAlt _) = error "VHDL.conToVHDLExpr Literals not support in case alternatives yet"
conToVHDLExpr DEFAULT = error "VHDL.conToVHDLExpr DEFAULT alternative should not occur here!"



{-
mkConcSm sigs (UncondDef src dst) _ = do
  src_expr <- vhdl_expr src
  let src_wform = AST.Wform [AST.WformElem src_expr Nothing]
  let dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
  let assign    = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)
  return $ AST.CSSASm assign
  where
    vhdl_expr (Left id) = return $ mkIdExpr sigs id
    vhdl_expr (Right expr) =
      case expr of
        (EqLit id lit) ->
          return $ (mkIdExpr sigs id) AST.:=: (AST.PrimLit lit)
        (Literal lit Nothing) ->
          return $ AST.PrimLit lit
        (Literal lit (Just ty)) -> do
          -- Create a cast expression, which is just a function call using the
          -- type name as the function name.
          let litexpr = AST.PrimLit lit
          ty_id <- vhdl_ty ty
          let ty_name = AST.NSimple ty_id
          let args = [Nothing AST.:=>: (AST.ADExpr litexpr)] 
          return $ AST.PrimFCall $ AST.FCall ty_name args
        (Eq a b) ->
         return $  (mkIdExpr sigs a) AST.:=: (mkIdExpr sigs b)

mkConcSm sigs (CondDef cond true false dst) _ =
  let
    cond_expr  = mkIdExpr sigs cond
    true_expr  = mkIdExpr sigs true
    false_expr  = mkIdExpr sigs false
    false_wform = AST.Wform [AST.WformElem false_expr Nothing]
    true_wform = AST.Wform [AST.WformElem true_expr Nothing]
    whenelse = AST.WhenElse true_wform cond_expr
    dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
    assign    = dst_name AST.:<==: (AST.ConWforms [whenelse] false_wform Nothing)
  in
    return $ AST.CSSASm assign
-}
-- | Turn a SignalId into a VHDL Expr
mkIdExpr :: [(SignalId, SignalInfo)] -> SignalId -> AST.Expr
mkIdExpr sigs id =
  let src_name  = AST.NSimple (getSignalId $ signalInfo sigs id) in
  AST.PrimName src_name

mkAssocElems :: 
  [CoreSyn.CoreExpr]            -- | The argument that are applied to function
  -> CoreSyn.CoreBndr           -- | The binder in which to store the result
  -> Entity                     -- | The entity to map against.
  -> [AST.AssocElem]            -- | The resulting port maps

mkAssocElems args res entity =
    -- Create the actual AssocElems
    Maybe.catMaybes $ zipWith mkAssocElem ports sigs
  where
    -- Turn the ports and signals from a map into a flat list. This works,
    -- since the maps must have an identical form by definition. TODO: Check
    -- the similar form?
    arg_ports = ent_args entity
    res_port  = ent_res entity
    -- Extract the id part from the (id, type) tuple
    ports     = map (Monad.liftM fst) (res_port : arg_ports)
    -- Translate signal numbers into names
    sigs      = (bndrToString res : map (bndrToString.varBndr) args)

-- Turns a Var CoreExpr into the Id inside it. Will of course only work for
-- simple Var CoreExprs, not complexer ones.
varBndr :: CoreSyn.CoreExpr -> Var.Id
varBndr (CoreSyn.Var id) = id

-- | Look up a signal in the signal name map
lookupSigName :: [(SignalId, SignalInfo)] -> SignalId -> String
lookupSigName sigs sig = name
  where
    info = Maybe.fromMaybe
      (error $ "Unknown signal " ++ (show sig) ++ " used? This should not happen!")
      (lookup sig sigs)
    name = Maybe.fromMaybe
      (error $ "Unnamed signal " ++ (show sig) ++ " used? This should not happen!")
      (sigName info)

-- | Create an VHDL port -> signal association
mkAssocElem :: Maybe AST.VHDLId -> String -> Maybe AST.AssocElem
mkAssocElem (Just port) signal = Just $ Just port AST.:=>: (AST.ADName (AST.NSimple (mkVHDLExtId signal))) 
mkAssocElem Nothing _ = Nothing

-- | The VHDL Bit type
bit_ty :: AST.TypeMark
bit_ty = AST.unsafeVHDLBasicId "Bit"

-- | The VHDL Boolean type
bool_ty :: AST.TypeMark
bool_ty = AST.unsafeVHDLBasicId "Boolean"

-- | The VHDL std_logic
std_logic_ty :: AST.TypeMark
std_logic_ty = AST.unsafeVHDLBasicId "std_logic"

-- Translate a Haskell type to a VHDL type
vhdl_ty :: Type.Type -> VHDLState AST.TypeMark
vhdl_ty ty = do
  typemap <- getA vsTypes
  let builtin_ty = do -- See if this is a tycon and lookup its name
        (tycon, args) <- Type.splitTyConApp_maybe ty
        let name = Name.getOccString (TyCon.tyConName tycon)
        Map.lookup name builtin_types
  -- If not a builtin type, try the custom types
  let existing_ty = (fmap fst) $ Map.lookup (OrdType ty) typemap
  case Monoid.getFirst $ Monoid.mconcat (map Monoid.First [builtin_ty, existing_ty]) of
    -- Found a type, return it
    Just t -> return t
    -- No type yet, try to construct it
    Nothing -> do
      newty_maybe <- (construct_vhdl_ty ty)
      case newty_maybe of
        Just (ty_id, ty_def) -> do
          -- TODO: Check name uniqueness
          modA vsTypes (Map.insert (OrdType ty) (ty_id, ty_def))
          return ty_id
        Nothing -> error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty)

-- Construct a new VHDL type for the given Haskell type.
construct_vhdl_ty :: Type.Type -> VHDLState (Maybe (AST.TypeMark, AST.TypeDef))
construct_vhdl_ty ty = do
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tycon)
      case name of
        "TFVec" -> do
          res <- mk_vector_ty (tfvec_len ty) ty
          return $ Just res
        "SizedWord" -> do
          res <- mk_vector_ty (sized_word_len ty) ty
          return $ Just res
        -- Create a custom type from this tycon
        otherwise -> mk_tycon_ty tycon args
    Nothing -> return $ Nothing

-- | Create VHDL type for a custom tycon
mk_tycon_ty :: TyCon.TyCon -> [Type.Type] -> VHDLState (Maybe (AST.TypeMark, AST.TypeDef))
mk_tycon_ty tycon args =
  case TyCon.tyConDataCons tycon of
    -- Not an algebraic type
    [] -> error $ "Only custom algebraic types are supported: " ++  (showSDoc $ ppr tycon)
    [dc] -> do
      let arg_tys = DataCon.dataConRepArgTys dc
      -- TODO: CoreSubst docs say each Subs can be applied only once. Is this a
      -- violation? Or does it only mean not to apply it again to the same
      -- subject?
      let real_arg_tys = map (CoreSubst.substTy subst) arg_tys
      elem_tys <- mapM vhdl_ty real_arg_tys
      let elems = zipWith AST.ElementDec recordlabels elem_tys
      -- For a single construct datatype, build a record with one field for
      -- each argument.
      -- TODO: Add argument type ids to this, to ensure uniqueness
      -- TODO: Special handling for tuples?
      let ty_id = mkVHDLExtId $ nameToString (TyCon.tyConName tycon)
      let ty_def = AST.TDR $ AST.RecordTypeDef elems
      return $ Just (ty_id, ty_def)
    dcs -> error $ "Only single constructor datatypes supported: " ++  (showSDoc $ ppr tycon)
  where
    -- Create a subst that instantiates all types passed to the tycon
    -- TODO: I'm not 100% sure that this is the right way to do this. It seems
    -- to work so far, though..
    tyvars = TyCon.tyConTyVars tycon
    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst (zip tyvars args)

-- | Create a VHDL vector type
mk_vector_ty ::
  Int -- ^ The length of the vector
  -> Type.Type -- ^ The Haskell type to create a VHDL type for
  -> VHDLState (AST.TypeMark, AST.TypeDef) -- The typemark created.

mk_vector_ty len ty = do
  -- Assume there is a single type argument
  let ty_id = mkVHDLExtId $ "vector_" ++ (show len)
  -- TODO: Use el_ty
  let range = AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len - 1))]
  let ty_def = AST.TDA $ AST.ConsArrayDef range std_logic_ty
  modA vsTypeFuns (Map.insert (OrdType ty) (genUnconsVectorFuns std_logic_ty ty_id))
  return (ty_id, ty_def)


builtin_types = 
  Map.fromList [
    ("Bit", std_logic_ty),
    ("Bool", bool_ty) -- TysWiredIn.boolTy
  ]

-- Shortcut for 
-- Can only contain alphanumerics and underscores. The supplied string must be
-- a valid basic id, otherwise an error value is returned. This function is
-- not meant to be passed identifiers from a source file, use mkVHDLExtId for
-- that.
mkVHDLBasicId :: String -> AST.VHDLId
mkVHDLBasicId s = 
  AST.unsafeVHDLBasicId $ (strip_multiscore . strip_leading . strip_invalid) s
  where
    -- Strip invalid characters.
    strip_invalid = filter (`elem` ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ "_.")
    -- Strip leading numbers and underscores
    strip_leading = dropWhile (`elem` ['0'..'9'] ++ "_")
    -- Strip multiple adjacent underscores
    strip_multiscore = concat . map (\cs -> 
        case cs of 
          ('_':_) -> "_"
          _ -> cs
      ) . List.group

-- Shortcut for Extended VHDL Id's. These Id's can contain a lot more
-- different characters than basic ids, but can never be used to refer to
-- basic ids.
-- Use extended Ids for any values that are taken from the source file.
mkVHDLExtId :: String -> AST.VHDLId
mkVHDLExtId s = 
  AST.unsafeVHDLExtId $ strip_invalid s
  where 
    -- Allowed characters, taken from ForSyde's mkVHDLExtId
    allowed = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ " \"#&\\'()*+,./:;<=>_|!$%@?[]^`{}~-"
    strip_invalid = filter (`elem` allowed)

-- Creates a VHDL Id from a binder
bndrToVHDLId ::
  CoreSyn.CoreBndr
  -> AST.VHDLId

bndrToVHDLId = mkVHDLExtId . OccName.occNameString . Name.nameOccName . Var.varName

-- Extracts the binder name as a String
bndrToString ::
  CoreSyn.CoreBndr
  -> String

bndrToString = OccName.occNameString . Name.nameOccName . Var.varName

-- Extracts the string version of the name
nameToString :: Name.Name -> String
nameToString = OccName.occNameString . Name.nameOccName

-- | A consise representation of a (set of) ports on a builtin function
--type PortMap = HsValueMap (String, AST.TypeMark)
-- | A consise representation of a builtin function
data BuiltIn = BuiltIn String [(String, AST.TypeMark)] (String, AST.TypeMark)

-- | Translate a list of concise representation of builtin functions to a
--   SignatureMap
mkBuiltins :: [BuiltIn] -> SignatureMap
mkBuiltins = Map.fromList . map (\(BuiltIn name args res) ->
    (name,
     Entity (VHDL.mkVHDLBasicId name) (map toVHDLSignalMapElement args) (toVHDLSignalMapElement res))
  )

builtin_hsfuncs = Map.keys builtin_funcs
builtin_funcs = mkBuiltins
  [ 
    BuiltIn "hwxor" [("a", VHDL.bit_ty), ("b", VHDL.bit_ty)] ("o", VHDL.bit_ty),
    BuiltIn "hwand" [("a", VHDL.bit_ty), ("b", VHDL.bit_ty)] ("o", VHDL.bit_ty),
    BuiltIn "hwor" [("a", VHDL.bit_ty), ("b", VHDL.bit_ty)] ("o", VHDL.bit_ty),
    BuiltIn "hwnot" [("a", VHDL.bit_ty)] ("o", VHDL.bit_ty)
  ]

recordlabels = map (\c -> mkVHDLBasicId [c]) ['A'..'Z']

-- | Map a port specification of a builtin function to a VHDL Signal to put in
--   a VHDLSignalMap
toVHDLSignalMapElement :: (String, AST.TypeMark) -> VHDLSignalMapElement
toVHDLSignalMapElement (name, ty) = Just (mkVHDLBasicId name, ty)
