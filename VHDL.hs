--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

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

import qualified Type
import qualified TysWiredIn
import qualified Name
import qualified TyCon
import Outputable ( showSDoc, ppr )

import qualified ForSyDe.Backend.VHDL.AST as AST

import VHDLTypes
import Flatten
import FlattenTypes
import TranslatorTypes
import HsValueMap
import Pretty

createDesignFiles ::
  FlatFuncMap
  -> [(AST.VHDLId, AST.DesignFile)]

createDesignFiles flatfuncmap =
  -- TODO: Output types
  (mkVHDLId "types", AST.DesignFile [] [type_package]) :
  map (Arrow.second $ AST.DesignFile context) units
  
  where
    init_session = VHDLSession Map.empty builtin_funcs
    (units, final_session) = 
      State.runState (createLibraryUnits flatfuncmap) init_session
    ty_decls = Map.elems (final_session ^. vsTypes)
    context = [
      AST.Library $ mkVHDLId "IEEE",
      AST.Use $ (AST.NSimple $ mkVHDLId "IEEE.std_logic_1164") AST.:.: AST.All,
      AST.Use $ (AST.NSimple $ mkVHDLId "work.types") AST.:.: AST.All]
    type_package = AST.LUPackageDec $ AST.PackageDec (mkVHDLId "types") (map (AST.PDITD . snd) ty_decls)

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

createEntity hsfunc flatfunc = 
      let 
        sigs    = flat_sigs flatfunc
        args    = flat_args flatfunc
        res     = flat_res  flatfunc
        (ty_decls, args') = Traversable.traverse (Traversable.traverse (mkMap sigs)) args
        (ty_decls', res') = Traversable.traverse (mkMap sigs) res
        -- TODO: Unique ty_decls
        ent_decl' = createEntityAST hsfunc args' res'
        AST.EntityDec entity_id _ = ent_decl' 
        signature = Entity entity_id args' res'
      in do
        modA vsSignatures (Map.insert hsfunc signature)
        return ent_decl'
  where
    mkMap :: 
      [(SignalId, SignalInfo)] 
      -> SignalId 
      -> ([AST.TypeDec], Maybe (AST.VHDLId, AST.TypeMark))
    mkMap sigmap id =
      if isPortSigUse $ sigUse info
        then
          let (decs, type_mark) = vhdl_ty ty in
          (decs, Just (mkVHDLId nm, type_mark))
        else
          (Monoid.mempty, Nothing)
      where
        info = Maybe.fromMaybe
          (error $ "Signal not found in the name map? This should not happen!")
          (lookup id sigmap)
        nm = Maybe.fromMaybe
          (error $ "Signal not named? This should not happen!")
          (sigName info)
        ty = sigTy info

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
        [AST.IfaceSigDec (mkVHDLId "clk") AST.In VHDL.std_logic_ty]
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
  mkVHDLId $ hsFuncName hsfunc

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
    -- Create concurrent statements for all signal definitions
  let statements = zipWith (mkConcSm signaturemap sigs) defs [0..]
  return $ AST.ArchBody (mkVHDLId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) (statements ++ procs')
  where
    sigs = flat_sigs flatfunc
    args = flat_args flatfunc
    res  = flat_res  flatfunc
    defs = flat_defs flatfunc
    -- Create signal declarations for all internal and state signals
    (ty_decls, sig_decs)  = Arrow.second Maybe.catMaybes $ Traversable.traverse (mkSigDec . snd) sigs
    -- TODO: Unique ty_decls
    -- TODO: Store ty_decls somewhere
    procs = map mkStateProcSm (makeStatePairs flatfunc)
    procs' = map AST.CSPSm procs

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
    label       = mkVHDLId $ "state_" ++ (show num)
    clk         = mkVHDLId "clk"
    rising_edge = AST.NSimple $ mkVHDLId "rising_edge"
    wform       = AST.Wform [AST.WformElem (AST.PrimName $ AST.NSimple $ getSignalId new) Nothing]
    assign      = AST.SigAssign (AST.NSimple $ getSignalId old) wform
    rising_edge_clk = AST.PrimFCall $ AST.FCall rising_edge [Nothing AST.:=>: (AST.ADName $ AST.NSimple clk)]
    statement   = AST.IfSm rising_edge_clk [assign] [] Nothing

mkSigDec :: SignalInfo -> ([AST.TypeDec], Maybe AST.SigDec)
mkSigDec info =
  let use = sigUse info in
  if isInternalSigUse use || isStateSigUse use then
    let (ty_decls, type_mark) = vhdl_ty ty in
    (ty_decls, Just $ AST.SigDec (getSignalId info) type_mark Nothing)
  else
    ([], Nothing)
  where
    ty = sigTy info

-- | Creates a VHDL Id from a named SignalInfo. Errors out if the SignalInfo
--   is not named.
getSignalId :: SignalInfo -> AST.VHDLId
getSignalId info =
    mkVHDLId $ Maybe.fromMaybe
      (error $ "Unnamed signal? This should not happen!")
      (sigName info)

-- | Transforms a signal definition into a VHDL concurrent statement
mkConcSm ::
  SignatureMap             -- ^ The interfaces of functions in the session
  -> [(SignalId, SignalInfo)] -- ^ The signals in the current architecture
  -> SigDef                -- ^ The signal definition 
  -> Int                   -- ^ A number that will be unique for all
                           --   concurrent statements in the architecture.
  -> AST.ConcSm            -- ^ The corresponding VHDL component instantiation.

mkConcSm signatures sigs (FApp hsfunc args res) num =
  let 
    signature = Maybe.fromMaybe
        (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' without signature? This should not happen!")
        (Map.lookup hsfunc signatures)
    entity_id = ent_id signature
    label = (AST.fromVHDLId entity_id) ++ "_" ++ (show num)
    -- Add a clk port if we have state
    clk_port = Maybe.fromJust $ mkAssocElem (Just $ mkVHDLId "clk") "clk"
    portmaps = mkAssocElems sigs args res signature ++ (if hasState hsfunc then [clk_port] else [])
  in
    AST.CSISm $ AST.CompInsSm (mkVHDLId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect portmaps)

mkConcSm _ sigs (UncondDef src dst) _ =
  let
    src_expr  = vhdl_expr src
    src_wform = AST.Wform [AST.WformElem src_expr Nothing]
    dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
    assign    = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)
  in
    AST.CSSASm assign
  where
    vhdl_expr (Left id) = mkIdExpr sigs id
    vhdl_expr (Right expr) =
      case expr of
        (EqLit id lit) ->
          (mkIdExpr sigs id) AST.:=: (AST.PrimLit lit)
        (Literal lit) ->
          AST.PrimLit lit
        (Eq a b) ->
          (mkIdExpr sigs a) AST.:=: (mkIdExpr sigs b)

mkConcSm _ sigs (CondDef cond true false dst) _ =
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
    AST.CSSASm assign

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
mkAssocElem (Just port) signal = Just $ Just port AST.:=>: (AST.ADName (AST.NSimple (mkVHDLId signal))) 
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
vhdl_ty :: Type.Type -> ([AST.TypeDec], AST.TypeMark)
vhdl_ty ty = Maybe.fromMaybe
  (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
  (vhdl_ty_maybe ty)

-- Translate a Haskell type to a VHDL type, optionally generating a type
-- declaration for the type.
vhdl_ty_maybe :: Type.Type -> Maybe ([AST.TypeDec], AST.TypeMark)
vhdl_ty_maybe ty =
  if Type.coreEqType ty TysWiredIn.boolTy
    then
      Just ([], bool_ty)
    else
      case Type.splitTyConApp_maybe ty of
        Just (tycon, args) ->
          let name = TyCon.tyConName tycon in
            -- TODO: Do something more robust than string matching
            case Name.getOccString name of
              "Bit"      -> Just ([], std_logic_ty)
              "FSVec"    ->
                let 
                  [len, el_ty] = args 
                  -- TODO: Find actual number
                  ty_id = mkVHDLId ("vector_" ++ (show len))
                  -- TODO: Use el_ty
                  range = AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit "16")]
                  ty_def = AST.TDA $ AST.ConsArrayDef range std_logic_ty
                  ty_dec = AST.TypeDec ty_id ty_def
                in
                  Just ([ty_dec], ty_id)
              otherwise  -> Nothing
        otherwise -> Nothing

-- Shortcut
mkVHDLId :: String -> AST.VHDLId
mkVHDLId s = 
  AST.unsafeVHDLBasicId $ (strip_multiscore . strip_invalid) s
  where
    -- Strip invalid characters.
    strip_invalid = filter (`elem` ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ "_.")
    -- Strip multiple adjacent underscores
    strip_multiscore = concat . map (\cs -> 
        case cs of 
          ('_':_) -> "_"
          _ -> cs
      ) . List.group

-- | A consise representation of a (set of) ports on a builtin function
type PortMap = HsValueMap (String, AST.TypeMark)
-- | A consise representation of a builtin function
data BuiltIn = BuiltIn String [PortMap] PortMap

-- | Translate a list of concise representation of builtin functions to a
--   SignatureMap
mkBuiltins :: [BuiltIn] -> SignatureMap
mkBuiltins = Map.fromList . map (\(BuiltIn name args res) ->
    (HsFunction name (map useAsPort args) (useAsPort res),
     Entity (VHDL.mkVHDLId name) (map toVHDLSignalMap args) (toVHDLSignalMap res))
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
toVHDLSignalMap = fmap (\(name, ty) -> Just (mkVHDLId name, ty))
