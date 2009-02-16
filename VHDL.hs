--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

import qualified Data.Foldable as Foldable
import qualified Maybe
import qualified Control.Monad as Monad

import qualified Type
import qualified Name
import qualified TyCon
import Outputable ( showSDoc, ppr )

import qualified ForSyDe.Backend.VHDL.AST as AST

import VHDLTypes
import FlattenTypes
import TranslatorTypes
import Pretty

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
    mkMap :: Eq id => [(id, SignalInfo)] -> id -> (AST.VHDLId, AST.TypeMark)
    mkMap sigmap id =
      (mkVHDLId nm, vhdl_ty ty)
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
    mapToPorts :: AST.Mode -> VHDLSignalMap -> [AST.IfaceSigDec] 
    mapToPorts mode m =
      map (mkIfaceSigDec mode) (Foldable.toList m)

-- | Create a port declaration
mkIfaceSigDec ::
  AST.Mode                         -- | The mode for the port (In / Out)
  -> (AST.VHDLId, AST.TypeMark)    -- | The id and type for the port
  -> AST.IfaceSigDec               -- | The resulting port declaration

mkIfaceSigDec mode (id, ty) = AST.IfaceSigDec id mode ty

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
      let apps = flat_apps flatfunc
      let entity_id = Maybe.fromMaybe
                      (error $ "Building architecture without an entity? This should not happen!")
                      (getEntityId fdata)
      -- Create signal declarations for all signals that are not in args and
      -- res
      let sig_decs = [mkSigDec info | (id, info) <- sigs, (all (id `Foldable.notElem`) (res:args)) ]
      -- Create component instantiations for all function applications
      insts <- mapM (mkCompInsSm sigs) apps
      let insts' = map AST.CSISm insts
      let arch = AST.ArchBody (mkVHDLId "structural") (AST.NSimple entity_id) (map AST.BDISD sig_decs) insts'
      setArchitecture hsfunc arch

mkSigDec :: SignalInfo -> AST.SigDec
mkSigDec info =
    AST.SigDec (mkVHDLId name) (vhdl_ty ty) Nothing
  where
    name = Maybe.fromMaybe
      (error $ "Unnamed signal? This should not happen!")
      (sigName info)
    ty = sigTy info

-- | Transforms a flat function application to a VHDL component instantiation.
mkCompInsSm ::
  [(UnnamedSignal, SignalInfo)] -- | The signals in the current architecture
  -> FApp UnnamedSignal         -- | The application to look at.
  -> VHDLState AST.CompInsSm    -- | The corresponding VHDL component instantiation.

mkCompInsSm sigs app = do
  let hsfunc = appFunc app
  fdata_maybe <- getFunc hsfunc
  let fdata = Maybe.fromMaybe
        (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' that is not in the session? This should not happen!")
        fdata_maybe
  let entity = Maybe.fromMaybe
        (error $ "Using function '" ++ (prettyShow hsfunc) ++ "' without entity declaration? This should not happen!")
        (funcEntity fdata)
  let entity_id = ent_id entity
  label <- uniqueName (AST.fromVHDLId entity_id)
  let portmaps = mkAssocElems sigs app entity
  return $ AST.CompInsSm (mkVHDLId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect portmaps)

mkAssocElems :: 
  [(UnnamedSignal, SignalInfo)] -- | The signals in the current architecture
  -> FApp UnnamedSignal         -- | The application to look at.
  -> Entity                     -- | The entity to map against.
  -> [AST.AssocElem]            -- | The resulting port maps

mkAssocElems sigmap app entity =
    -- Create the actual AssocElems
    zipWith mkAssocElem ports sigs
  where
    -- Turn the ports and signals from a map into a flat list. This works,
    -- since the maps must have an identical form by definition. TODO: Check
    -- the similar form?
    arg_ports = concat (map Foldable.toList (ent_args entity))
    res_ports = Foldable.toList (ent_res entity)
    arg_sigs  = (concat (map Foldable.toList (appArgs app)))
    res_sigs  = Foldable.toList (appRes app)
    -- Extract the id part from the (id, type) tuple
    ports     = (map fst (arg_ports ++ res_ports)) 
    -- Translate signal numbers into names
    sigs      = (map (lookupSigName sigmap) (arg_sigs ++ res_sigs))

-- | Look up a signal in the signal name map
lookupSigName :: [(UnnamedSignal, SignalInfo)] -> UnnamedSignal -> String
lookupSigName sigs sig = name
  where
    info = Maybe.fromMaybe
      (error $ "Unknown signal " ++ (show sig) ++ " used? This should not happen!")
      (lookup sig sigs)
    name = Maybe.fromMaybe
      (error $ "Unnamed signal " ++ (show sig) ++ " used? This should not happen!")
      (sigName info)

-- | Create an VHDL port -> signal association
mkAssocElem :: AST.VHDLId -> String -> AST.AssocElem
mkAssocElem port signal = Just port AST.:=>: (AST.ADName (AST.NSimple (mkVHDLId signal))) 

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
  -> [AST.LibraryUnit]        -- | The library units it generates

getLibraryUnits (hsfunc, fdata) =
  case funcEntity fdata of 
    Nothing -> []
    Just ent -> case ent_decl ent of
      Nothing -> []
      Just decl -> [AST.LUEntity decl]
  ++
  case funcArch fdata of
    Nothing -> []
    Just arch -> [AST.LUArch arch]

-- | The VHDL Bit type
bit_ty :: AST.TypeMark
bit_ty = AST.unsafeVHDLBasicId "Bit"

-- Translate a Haskell type to a VHDL type
vhdl_ty :: Type.Type -> AST.TypeMark
vhdl_ty ty = Maybe.fromMaybe
  (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
  (vhdl_ty_maybe ty)

-- Translate a Haskell type to a VHDL type
vhdl_ty_maybe :: Type.Type -> Maybe AST.TypeMark
vhdl_ty_maybe ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) ->
      let name = TyCon.tyConName tycon in
        -- TODO: Do something more robust than string matching
        case Name.getOccString name of
          "Bit"      -> Just bit_ty
          otherwise  -> Nothing
    otherwise -> Nothing

-- Shortcut
mkVHDLId :: String -> AST.VHDLId
mkVHDLId = AST.unsafeVHDLBasicId
