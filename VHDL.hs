--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

import qualified Data.Foldable as Foldable
import qualified Maybe
import qualified Control.Monad as Monad

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
import Pretty

getDesignFiles :: VHDLState [AST.DesignFile]
getDesignFiles = do
  -- Extract the library units generated from all the functions in the
  -- session.
  funcs <- getFuncs
  let units = Maybe.mapMaybe getLibraryUnits funcs
  let context = [
        AST.Library $ mkVHDLId "IEEE",
        AST.Use $ (AST.NSimple $ mkVHDLId "IEEE.std_logic_1164") AST.:.: AST.All]
  return $ map (\(ent, arch) -> AST.DesignFile context [ent, arch]) units
  
-- | Create an entity for a given function
createEntity ::
  HsFunction        -- | The function signature
  -> FuncData       -- | The function data collected so far
  -> VHDLState ()

createEntity hsfunc fdata = 
  let func = flatFunc fdata in
  case func of
    -- Skip (builtin) functions without a FlatFunction
    Nothing -> do return ()
    -- Create an entity for all other functions
    Just flatfunc ->
      
      let 
        sigs    = flat_sigs flatfunc
        args    = flat_args flatfunc
        res     = flat_res  flatfunc
        args'   = map (fmap (mkMap sigs)) args
        res'    = fmap (mkMap sigs) res
        ent_decl' = createEntityAST hsfunc args' res'
        AST.EntityDec entity_id _ = ent_decl' 
        entity' = Entity entity_id args' res' (Just ent_decl')
      in
        setEntity hsfunc entity'
  where
    mkMap :: Eq id => [(id, SignalInfo)] -> id -> Maybe (AST.VHDLId, AST.TypeMark)
    mkMap sigmap id =
      if isPortSigUse $ sigUse info
        then
          Just (mkVHDLId nm, vhdl_ty ty)
        else
          Nothing
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
  HsFunction        -- | The function signature
  -> FuncData       -- | The function data collected so far
  -> VHDLState ()

createArchitecture hsfunc fdata = 
  let func = flatFunc fdata in
  case func of
    -- Skip (builtin) functions without a FlatFunction
    Nothing -> do return ()
    -- Create an architecture for all other functions
    Just flatfunc -> do
      let sigs = flat_sigs flatfunc
      let args = flat_args flatfunc
      let res  = flat_res  flatfunc
      let defs = flat_defs flatfunc
      let entity_id = Maybe.fromMaybe
                      (error $ "Building architecture without an entity? This should not happen!")
                      (getEntityId fdata)
      -- Create signal declarations for all signals that are not in args and
      -- res
      let sig_decs = Maybe.catMaybes $ map (mkSigDec . snd) sigs
      -- Create concurrent statements for all signal definitions
      statements <- mapM (mkConcSm sigs) defs
      let procs = map mkStateProcSm (getOwnStates hsfunc flatfunc)
      let procs' = map AST.CSPSm procs
      let arch = AST.ArchBody (mkVHDLId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) (statements ++ procs')
      setArchitecture hsfunc arch

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

mkSigDec :: SignalInfo -> Maybe AST.SigDec
mkSigDec info =
  let use = sigUse info in
  if isInternalSigUse use || isStateSigUse use then
    Just $ AST.SigDec (getSignalId info) (vhdl_ty ty) Nothing
  else
    Nothing
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
  [(SignalId, SignalInfo)] -- | The signals in the current architecture
  -> SigDef                -- | The signal definition
  -> VHDLState AST.ConcSm    -- | The corresponding VHDL component instantiation.

mkConcSm sigs (FApp hsfunc args res) = do
  fdata_maybe <- getFunc hsfunc
  let fdata = Maybe.fromMaybe
        (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' that is not in the session? This should not happen!")
        fdata_maybe
  let entity = Maybe.fromMaybe
        (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' without entity declaration? This should not happen!")
        (funcEntity fdata)
  let entity_id = ent_id entity
  label <- uniqueName (AST.fromVHDLId entity_id)
  let portmaps = mkAssocElems sigs args res entity
  return $ AST.CSISm $ AST.CompInsSm (mkVHDLId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect portmaps)

mkConcSm sigs (UncondDef src dst) = do
  let src_expr  = vhdl_expr src
  let src_wform = AST.Wform [AST.WformElem src_expr Nothing]
  let dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
  let assign    = dst_name AST.:<==: (AST.ConWforms [] src_wform Nothing)
  return $ AST.CSSASm assign
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

mkConcSm sigs (CondDef cond true false dst) = do
  let cond_expr  = mkIdExpr sigs cond
  let true_expr  = mkIdExpr sigs true
  let false_expr  = mkIdExpr sigs false
  let false_wform = AST.Wform [AST.WformElem false_expr Nothing]
  let true_wform = AST.Wform [AST.WformElem true_expr Nothing]
  let whenelse = AST.WhenElse true_wform cond_expr
  let dst_name  = AST.NSimple (getSignalId $ signalInfo sigs dst)
  let assign    = dst_name AST.:<==: (AST.ConWforms [whenelse] false_wform Nothing)
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
mkAssocElem (Just port) signal = Just $ Just port AST.:=>: (AST.ADName (AST.NSimple (mkVHDLId signal))) 
mkAssocElem Nothing _ = Nothing

-- | Extracts the generated entity id from the given funcdata
getEntityId :: FuncData -> Maybe AST.VHDLId
getEntityId fdata =
  case funcEntity fdata of
    Nothing -> Nothing
    Just e  -> case ent_decl e of
      Nothing -> Nothing
      Just (AST.EntityDec id _) -> Just id

getLibraryUnits ::
  (HsFunction, FuncData)      -- | A function from the session
  -> Maybe (AST.LibraryUnit, AST.LibraryUnit) -- | The entity and architecture for the function

getLibraryUnits (hsfunc, fdata) =
  case funcEntity fdata of 
    Nothing -> Nothing
    Just ent -> 
      case ent_decl ent of
      Nothing -> Nothing
      Just decl ->
        case funcArch fdata of
          Nothing -> Nothing
          Just arch ->
            Just (AST.LUEntity decl, AST.LUArch arch)

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
vhdl_ty :: Type.Type -> AST.TypeMark
vhdl_ty ty = Maybe.fromMaybe
  (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
  (vhdl_ty_maybe ty)

-- Translate a Haskell type to a VHDL type
vhdl_ty_maybe :: Type.Type -> Maybe AST.TypeMark
vhdl_ty_maybe ty =
  if Type.coreEqType ty TysWiredIn.boolTy
    then
      Just bool_ty
    else
      case Type.splitTyConApp_maybe ty of
        Just (tycon, args) ->
          let name = TyCon.tyConName tycon in
            -- TODO: Do something more robust than string matching
            case Name.getOccString name of
              "Bit"      -> Just std_logic_ty
              otherwise  -> Nothing
        otherwise -> Nothing

-- Shortcut
mkVHDLId :: String -> AST.VHDLId
mkVHDLId s = 
  AST.unsafeVHDLBasicId s'
  where
    -- Strip invalid characters.
    s' = filter (`elem` ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ "_.") s
