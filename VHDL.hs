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

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import qualified Type
import qualified Name
import qualified TyCon
import Outputable ( showSDoc, ppr )

-- Local imports
import VHDLTypes
import Flatten
import FlattenTypes
import TranslatorTypes
import HsValueMap
import Pretty
import CoreTools

createDesignFiles ::
  FlatFuncMap
  -> [(AST.VHDLId, AST.DesignFile)]

createDesignFiles flatfuncmap =
  (mkVHDLBasicId "types", AST.DesignFile ieee_context [type_package]) :
  map (Arrow.second $ AST.DesignFile full_context) units
  
  where
    init_session = VHDLSession Map.empty builtin_funcs
    (units, final_session) = 
      State.runState (createLibraryUnits flatfuncmap) init_session
    ty_decls = Map.elems (final_session ^. vsTypes)
    ieee_context = [
        AST.Library $ mkVHDLBasicId "IEEE",
        mkUseAll ["IEEE", "std_logic_1164"],
        mkUseAll ["IEEE", "numeric_std"]
      ]
    full_context =
      mkUseAll ["work", "types"]
      : ieee_context
    type_package = AST.LUPackageDec $ AST.PackageDec (mkVHDLBasicId "types") (map (AST.PDITD . snd) ty_decls)

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
  FlatFuncMap
  -> VHDLState [(AST.VHDLId, [AST.LibraryUnit])]

createLibraryUnits flatfuncmap = do
  let hsfuncs = Map.keys flatfuncmap
  let flatfuncs = Map.elems flatfuncmap
  entities <- Monad.zipWithM createEntity hsfuncs flatfuncs
  archs <- Monad.zipWithM createArchitecture hsfuncs flatfuncs
  return $ zipWith 
    (\ent arch -> 
      let AST.EntityDec id _ = ent in 
      (id, [AST.LUEntity ent, AST.LUArch arch])
    )
    entities archs

-- | Create an entity for a given function
createEntity ::
  HsFunction -- | The function signature
  -> FlatFunction -- | The FlatFunction
  -> VHDLState AST.EntityDec -- | The resulting entity

createEntity hsfunc flatfunc = do
      let sigs    = flat_sigs flatfunc
      let args    = flat_args flatfunc
      let res     = flat_res  flatfunc
      args' <- Traversable.traverse (Traversable.traverse (mkMap sigs)) args
      res' <- Traversable.traverse (mkMap sigs) res
      let ent_decl' = createEntityAST hsfunc args' res'
      let AST.EntityDec entity_id _ = ent_decl' 
      let signature = Entity entity_id args' res'
      modA vsSignatures (Map.insert hsfunc signature)
      return ent_decl'
  where
    mkMap :: 
      [(SignalId, SignalInfo)] 
      -> SignalId 
      -> VHDLState VHDLSignalMapElement
    -- We only need the vsTypes element from the state
    mkMap sigmap = MonadState.lift vsTypes . (\id ->
      let
        info = Maybe.fromMaybe
          (error $ "Signal not found in the name map? This should not happen!")
          (lookup id sigmap)
        nm = Maybe.fromMaybe
          (error $ "Signal not named? This should not happen!")
          (sigName info)
        ty = sigTy info
      in
        if isPortSigUse $ sigUse info
          then do
            type_mark <- vhdl_ty ty
            return $ Just (mkVHDLExtId nm, type_mark)
          else
            return $ Nothing
       )

  -- | Create the VHDL AST for an entity
createEntityAST ::
  HsFunction            -- | The signature of the function we're working with
  -> [VHDLSignalMap]    -- | The entity's arguments
  -> VHDLSignalMap      -- | The entity's result
  -> AST.EntityDec      -- | The entity with the ent_decl filled in as well

createEntityAST hsfunc args res =
  AST.EntityDec vhdl_id ports
  where
    vhdl_id = mkEntityId hsfunc
    ports = concatMap (mapToPorts AST.In) args
            ++ mapToPorts AST.Out res
            ++ clk_port
    mapToPorts :: AST.Mode -> VHDLSignalMap -> [AST.IfaceSigDec] 
    mapToPorts mode m =
      Maybe.catMaybes $ map (mkIfaceSigDec mode) (Foldable.toList m)
    -- Add a clk port if we have state
    clk_port = if hasState hsfunc
      then
        [AST.IfaceSigDec (mkVHDLExtId "clk") AST.In VHDL.std_logic_ty]
      else
        []

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
  HsFunction -- ^ The function signature
  -> FlatFunction -- ^ The FlatFunction
  -> VHDLState AST.ArchBody -- ^ The architecture for this function

createArchitecture hsfunc flatfunc = do
  signaturemap <- getA vsSignatures
  let signature = Maybe.fromMaybe 
        (error $ "Generating architecture for function " ++ (prettyShow hsfunc) ++ "without signature? This should not happen!")
        (Map.lookup hsfunc signaturemap)
  let entity_id = ent_id signature
  -- Create signal declarations for all internal and state signals
  sig_dec_maybes <- mapM (mkSigDec' . snd) sigs
  let sig_decs = Maybe.catMaybes $ sig_dec_maybes
  -- Create concurrent statements for all signal definitions
  statements <- Monad.zipWithM (mkConcSm sigs) defs [0..]
  return $ AST.ArchBody (mkVHDLBasicId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) (statements ++ procs')
  where
    sigs = flat_sigs flatfunc
    args = flat_args flatfunc
    res  = flat_res  flatfunc
    defs = flat_defs flatfunc
    procs = map mkStateProcSm (makeStatePairs flatfunc)
    procs' = map AST.CSPSm procs
    -- mkSigDec only uses vsTypes from the state
    mkSigDec' = MonadState.lift vsTypes . mkSigDec

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

mkSigDec :: SignalInfo -> TypeState (Maybe AST.SigDec)
mkSigDec info =
  let use = sigUse info in
  if isInternalSigUse use || isStateSigUse use then do
    type_mark <- vhdl_ty ty
    return $ Just (AST.SigDec (getSignalId info) type_mark Nothing)
  else
    return Nothing
  where
    ty = sigTy info

-- | Creates a VHDL Id from a named SignalInfo. Errors out if the SignalInfo
--   is not named.
getSignalId :: SignalInfo -> AST.VHDLId
getSignalId info =
    mkVHDLExtId $ Maybe.fromMaybe
      (error $ "Unnamed signal? This should not happen!")
      (sigName info)

-- | Transforms a signal definition into a VHDL concurrent statement
mkConcSm ::
  [(SignalId, SignalInfo)] -- ^ The signals in the current architecture
  -> SigDef                -- ^ The signal definition 
  -> Int                   -- ^ A number that will be unique for all
                           --   concurrent statements in the architecture.
  -> VHDLState AST.ConcSm  -- ^ The corresponding VHDL component instantiation.

mkConcSm sigs (FApp hsfunc args res) num = do
  signatures <- getA vsSignatures
  let 
      signature = Maybe.fromMaybe
          (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' without signature? This should not happen!")
          (Map.lookup hsfunc signatures)
      entity_id = ent_id signature
      label = (AST.fromVHDLId entity_id) ++ "_" ++ (show num)
      -- Add a clk port if we have state
      clk_port = Maybe.fromJust $ mkAssocElem (Just $ mkVHDLExtId "clk") "clk"
      portmaps = mkAssocElems sigs args res signature ++ (if hasState hsfunc then [clk_port] else [])
    in
      return $ AST.CSISm $ AST.CompInsSm (mkVHDLExtId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect portmaps)

mkConcSm sigs (UncondDef src dst) _ =
  let
    src_expr  = vhdl_expr src
    src_wform = AST.Wform [AST.WformElem src_expr Nothing]
    dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
    assign    = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)
  in
    return $ AST.CSSASm assign
  where
    vhdl_expr (Left id) = mkIdExpr sigs id
    vhdl_expr (Right expr) =
      case expr of
        (EqLit id lit) ->
          (mkIdExpr sigs id) AST.:=: (AST.PrimLit lit)
        (Literal lit _) ->
          AST.PrimLit lit
        (Eq a b) ->
          (mkIdExpr sigs a) AST.:=: (mkIdExpr sigs b)

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

-- | Turn a SignalId into a VHDL Expr
mkIdExpr :: [(SignalId, SignalInfo)] -> SignalId -> AST.Expr
mkIdExpr sigs id =
  let src_name  = AST.NSimple (getSignalId $ signalInfo sigs id) in
  AST.PrimName src_name

mkAssocElems :: 
  [(SignalId, SignalInfo)]      -- | The signals in the current architecture
  -> [SignalMap]                -- | The signals that are applied to function
  -> SignalMap                  -- | the signals in which to store the function result
  -> Entity                     -- | The entity to map against.
  -> [AST.AssocElem]            -- | The resulting port maps

mkAssocElems sigmap args res entity =
    -- Create the actual AssocElems
    Maybe.catMaybes $ zipWith mkAssocElem ports sigs
  where
    -- Turn the ports and signals from a map into a flat list. This works,
    -- since the maps must have an identical form by definition. TODO: Check
    -- the similar form?
    arg_ports = concat (map Foldable.toList (ent_args entity))
    res_ports = Foldable.toList (ent_res entity)
    arg_sigs  = (concat (map Foldable.toList args))
    res_sigs  = Foldable.toList res
    -- Extract the id part from the (id, type) tuple
    ports     = (map (fmap fst) (arg_ports ++ res_ports)) 
    -- Translate signal numbers into names
    sigs      = (map (lookupSigName sigmap) (arg_sigs ++ res_sigs))

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
vhdl_ty :: Type.Type -> TypeState AST.TypeMark
vhdl_ty ty = do
  typemap <- State.get
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
      let new_ty = do
            -- Use the Maybe Monad for failing when one of these fails
            (tycon, args) <- Type.splitTyConApp_maybe ty
            let name = Name.getOccString (TyCon.tyConName tycon)
            case name of
              "FSVec" -> Just $ mk_vector_ty (fsvec_len ty) ty
              "SizedWord" -> Just $ mk_vector_ty (sized_word_len ty) ty
              otherwise -> Nothing
      -- Return new_ty when a new type was successfully created
      Maybe.fromMaybe 
        (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
        new_ty

-- | Create a VHDL vector type
mk_vector_ty ::
  Int -- ^ The length of the vector
  -> Type.Type -- ^ The Haskell type to create a VHDL type for
  -> TypeState AST.TypeMark -- The typemark created.

mk_vector_ty len ty = do
  -- Assume there is a single type argument
  let ty_id = mkVHDLExtId $ "vector_" ++ (show len)
  -- TODO: Use el_ty
  let range = AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len - 1))]
  let ty_def = AST.TDA $ AST.ConsArrayDef range std_logic_ty
  let ty_dec = AST.TypeDec ty_id ty_def
  -- TODO: Check name uniqueness
  State.modify (Map.insert (OrdType ty) (ty_id, ty_dec))
  return ty_id


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

-- | A consise representation of a (set of) ports on a builtin function
type PortMap = HsValueMap (String, AST.TypeMark)
-- | A consise representation of a builtin function
data BuiltIn = BuiltIn String [PortMap] PortMap

-- | Translate a list of concise representation of builtin functions to a
--   SignatureMap
mkBuiltins :: [BuiltIn] -> SignatureMap
mkBuiltins = Map.fromList . map (\(BuiltIn name args res) ->
    (HsFunction name (map useAsPort args) (useAsPort res),
     Entity (VHDL.mkVHDLBasicId name) (map toVHDLSignalMap args) (toVHDLSignalMap res))
  )

builtin_hsfuncs = Map.keys builtin_funcs
builtin_funcs = mkBuiltins
  [ 
    BuiltIn "hwxor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwand" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwor" [(Single ("a", VHDL.bit_ty)), (Single ("b", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty)),
    BuiltIn "hwnot" [(Single ("a", VHDL.bit_ty))] (Single ("o", VHDL.bit_ty))
  ]

-- | Map a port specification of a builtin function to a VHDL Signal to put in
--   a VHDLSignalMap
toVHDLSignalMap :: HsValueMap (String, AST.TypeMark) -> VHDLSignalMap
toVHDLSignalMap = fmap (\(name, ty) -> Just (mkVHDLBasicId name, ty))
