{-# LANGUAGE RelaxedPolyRec #-} -- Needed for vhdl_ty_either', for some reason...
module CLasH.VHDL.VHDLTools where

-- Standard modules
import qualified Maybe
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Char as Char
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Data.Accessor.Monad.Trans.State as MonadState

-- VHDL Imports
import qualified Language.VHDL.AST as AST

-- GHC API
import qualified CoreSyn
import qualified Name
import qualified OccName
import qualified Var
import qualified Id
import qualified TyCon
import qualified Type
import qualified DataCon
import qualified CoreSubst
import qualified Outputable

-- Local imports
import CLasH.VHDL.VHDLTypes
import CLasH.Translator.TranslatorTypes
import CLasH.Utils.Core.CoreTools
import CLasH.Utils
import CLasH.Utils.Pretty
import CLasH.VHDL.Constants

-----------------------------------------------------------------------------
-- Functions to generate concurrent statements
-----------------------------------------------------------------------------

-- Create an unconditional assignment statement
mkUncondAssign ::
  Either CoreSyn.CoreBndr AST.VHDLName -- ^ The signal to assign to
  -> AST.Expr -- ^ The expression to assign
  -> AST.ConcSm -- ^ The resulting concurrent statement
mkUncondAssign dst expr = mkAssign dst Nothing expr

-- Create a conditional assignment statement
mkCondAssign ::
  Either CoreSyn.CoreBndr AST.VHDLName -- ^ The signal to assign to
  -> AST.Expr -- ^ The condition
  -> AST.Expr -- ^ The value when true
  -> AST.Expr -- ^ The value when false
  -> AST.ConcSm -- ^ The resulting concurrent statement
mkCondAssign dst cond true false = mkAssign dst (Just (cond, true)) false

-- Create a conditional or unconditional assignment statement
mkAssign ::
  Either CoreSyn.CoreBndr AST.VHDLName -- ^ The signal to assign to
  -> Maybe (AST.Expr , AST.Expr) -- ^ Optionally, the condition to test for
                                 -- and the value to assign when true.
  -> AST.Expr -- ^ The value to assign when false or no condition
  -> AST.ConcSm -- ^ The resulting concurrent statement
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
      Left bndr -> AST.NSimple (varToVHDLId bndr)
      Right name -> name
    assign    = dst_name AST.:<==: (AST.ConWforms whenelse false_wform Nothing)
  in
    AST.CSSASm assign

mkAltsAssign ::
  Either CoreSyn.CoreBndr AST.VHDLName            -- ^ The signal to assign to
  -> [AST.Expr]       -- ^ The conditions
  -> [AST.Expr]       -- ^ The expressions
  -> AST.ConcSm   -- ^ The Alt assigns
mkAltsAssign dst conds exprs
        | (length conds) /= ((length exprs) - 1) = error "\nVHDLTools.mkAltsAssign: conditions expression mismatch"
        | otherwise =
  let
    whenelses   = zipWith mkWhenElse conds exprs
    false_wform = AST.Wform [AST.WformElem (last exprs) Nothing]
    dst_name  = case dst of
      Left bndr -> AST.NSimple (varToVHDLId bndr)
      Right name -> name
    assign    = dst_name AST.:<==: (AST.ConWforms whenelses false_wform Nothing)
  in
    AST.CSSASm assign
  where
    mkWhenElse :: AST.Expr -> AST.Expr -> AST.WhenElse
    mkWhenElse cond true_expr =
      let
        true_wform = AST.Wform [AST.WformElem true_expr Nothing]
      in
        AST.WhenElse true_wform cond

mkAssocElems :: 
  [AST.Expr]                    -- ^ The argument that are applied to function
  -> AST.VHDLName               -- ^ The binder in which to store the result
  -> Entity                     -- ^ The entity to map against.
  -> [AST.AssocElem]            -- ^ The resulting port maps
mkAssocElems args res entity =
    arg_maps ++ (Maybe.maybeToList res_map_maybe)
  where
    arg_ports = ent_args entity
    res_port_maybe = ent_res entity
    -- Create an expression of res to map against the output port
    res_expr = vhdlNameToVHDLExpr res
    -- Map each of the input ports
    arg_maps = zipWith mkAssocElem (map fst arg_ports) args
    -- Map the output port, if present
    res_map_maybe = fmap (\port -> mkAssocElem (fst port) res_expr) res_port_maybe

-- | Create an VHDL port -> signal association
mkAssocElem :: AST.VHDLId -> AST.Expr -> AST.AssocElem
mkAssocElem port signal = Just port AST.:=>: (AST.ADExpr signal) 

-- | Create an aggregate signal
mkAggregateSignal :: [AST.Expr] -> AST.Expr
mkAggregateSignal x = AST.Aggregate (map (\z -> AST.ElemAssoc Nothing z) x)

mkComponentInst ::
  String -- ^ The portmap label
  -> AST.VHDLId -- ^ The entity name
  -> [AST.AssocElem] -- ^ The port assignments
  -> AST.ConcSm
mkComponentInst label entity_id portassigns = AST.CSISm compins
  where
    -- We always have a clock port, so no need to map it anywhere but here
    clk_port = mkAssocElem clockId (idToVHDLExpr clockId)
    resetn_port = mkAssocElem resetId (idToVHDLExpr resetId)
    compins = AST.CompInsSm (mkVHDLExtId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect (portassigns ++ [clk_port,resetn_port]))

-----------------------------------------------------------------------------
-- Functions to generate VHDL Exprs
-----------------------------------------------------------------------------

varToVHDLExpr :: Var.Var -> TypeSession AST.Expr
varToVHDLExpr var =
  case Id.isDataConWorkId_maybe var of
    -- This is a dataconstructor.
    Just dc -> dataconToVHDLExpr dc
    -- Not a datacon, just another signal.
    Nothing -> return $ AST.PrimName $ AST.NSimple $ varToVHDLId var

-- Turn a VHDLName into an AST expression
vhdlNameToVHDLExpr = AST.PrimName

-- Turn a VHDL Id into an AST expression
idToVHDLExpr = vhdlNameToVHDLExpr . AST.NSimple

-- Turn a Core expression into an AST expression
exprToVHDLExpr core = varToVHDLExpr (exprToVar core)

-- Turn a alternative constructor into an AST expression. For
-- dataconstructors, this is only the constructor itself, not any arguments it
-- has. Should not be called with a DEFAULT constructor.
altconToVHDLExpr :: CoreSyn.AltCon -> TypeSession AST.Expr
altconToVHDLExpr (CoreSyn.DataAlt dc) = dataconToVHDLExpr dc

altconToVHDLExpr (CoreSyn.LitAlt _) = error "\nVHDL.conToVHDLExpr: Literals not support in case alternatives yet"
altconToVHDLExpr CoreSyn.DEFAULT = error "\nVHDL.conToVHDLExpr: DEFAULT alternative should not occur here!"

-- Turn a datacon (without arguments!) into a VHDL expression.
dataconToVHDLExpr :: DataCon.DataCon -> TypeSession AST.Expr
dataconToVHDLExpr dc = do
  typemap <- MonadState.get tsTypes
  htype_either <- mkHTypeEither (DataCon.dataConRepType dc)
  case htype_either of
    -- No errors
    Right htype -> do
      let dcname = DataCon.dataConName dc
      case htype of
        (BuiltinType "Bit") -> return $ AST.PrimLit $ case Name.getOccString dcname of "High" -> "'1'"; "Low" -> "'0'"
        (BuiltinType "Bool") -> return $ AST.PrimLit $ case Name.getOccString dcname of "True" -> "true"; "False" -> "false"
        otherwise -> do
          let existing_ty = Monad.liftM (fmap fst) $ Map.lookup htype typemap
          case existing_ty of
            Just ty -> do
              let lit    = idToVHDLExpr $ mkVHDLExtId $ Name.getOccString dcname
              return lit
            Nothing -> error $ "\nVHDLTools.dataconToVHDLExpr: Trying to make value for non-representable DataCon: " ++ pprString dc
    -- Error when constructing htype
    Left err -> error err

-----------------------------------------------------------------------------
-- Functions dealing with names, variables and ids
-----------------------------------------------------------------------------

-- Creates a VHDL Id from a binder
varToVHDLId ::
  CoreSyn.CoreBndr
  -> AST.VHDLId
varToVHDLId var = mkVHDLExtId (varToString var ++ varToStringUniq var ++ show (lowers $ varToStringUniq var))
  where
    lowers :: String -> Int
    lowers xs = length [x | x <- xs, Char.isLower x]

-- Creates a VHDL Name from a binder
varToVHDLName ::
  CoreSyn.CoreBndr
  -> AST.VHDLName
varToVHDLName = AST.NSimple . varToVHDLId

-- Extracts the binder name as a String
varToString ::
  CoreSyn.CoreBndr
  -> String
varToString = OccName.occNameString . Name.nameOccName . Var.varName

-- Get the string version a Var's unique
varToStringUniq :: Var.Var -> String
varToStringUniq = show . Var.varUnique

-- Extracts the string version of the name
nameToString :: Name.Name -> String
nameToString = OccName.occNameString . Name.nameOccName

-- Shortcut for Basic VHDL Ids.
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
    strip_multiscore = concatMap (\cs -> 
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
    allowed = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ " \"#&'()*+,./:;<=>_|!$%@?[]^`{}~-"
    strip_invalid = filter (`elem` allowed)

-- Create a record field selector that selects the given label from the record
-- stored in the given binder.
mkSelectedName :: AST.VHDLName -> AST.VHDLId -> AST.VHDLName
mkSelectedName name label =
   AST.NSelected $ name AST.:.: (AST.SSimple label) 

-- Create an indexed name that selects a given element from a vector.
mkIndexedName :: AST.VHDLName -> AST.Expr -> AST.VHDLName
-- Special case for already indexed names. Just add an index
mkIndexedName (AST.NIndexed (AST.IndexedName name indexes)) index =
 AST.NIndexed (AST.IndexedName name (indexes++[index]))
-- General case for other names
mkIndexedName name index = AST.NIndexed (AST.IndexedName name [index])

-----------------------------------------------------------------------------
-- Functions dealing with VHDL types
-----------------------------------------------------------------------------
builtin_types :: TypeMap
builtin_types = 
  Map.fromList [
    (BuiltinType "Bit", Just (std_logicTM, Nothing)),
    (BuiltinType "Bool", Just (booleanTM, Nothing)) -- TysWiredIn.boolTy
  ]

-- Is the given type representable at runtime?
isReprType :: Type.Type -> TypeSession Bool
isReprType ty = do
  ty_either <- mkHTypeEither ty
  return $ case ty_either of
    Left _ -> False
    Right _ -> True

-- | Turn a Core type into a HType, returning an error using the given
-- error string if the type was not representable.
mkHType :: (TypedThing t, Outputable.Outputable t) => 
  String -> t -> TypeSession HType
mkHType msg ty = do
  htype_either <- mkHTypeEither ty
  case htype_either of
    Right htype -> return htype
    Left err -> error $ msg ++ err  

-- | Turn a Core type into a HType. Returns either an error message if
-- the type was not representable, or the HType generated.
mkHTypeEither :: (TypedThing t, Outputable.Outputable t) => 
  t -> TypeSession (Either String HType)
mkHTypeEither tything =
  case getType tything of
    Nothing -> return $ Left $ "\nVHDLTools.mkHTypeEither: Typed thing without a type: " ++ pprString tything
    Just ty -> mkHTypeEither' ty

mkHTypeEither' :: Type.Type -> TypeSession (Either String HType)
mkHTypeEither' ty | ty_has_free_tyvars ty = return $ Left $ "\nVHDLTools.mkHTypeEither': Cannot create type: type has free type variables: " ++ pprString ty
                  | isStateType ty = return $ Right StateType
                  | otherwise =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) -> do
      typemap <- MonadState.get tsTypes
      let name = Name.getOccString (TyCon.tyConName tycon)
      let builtinTyMaybe = Map.lookup (BuiltinType name) typemap  
      case builtinTyMaybe of
        (Just x) -> return $ Right $ BuiltinType name
        Nothing ->
          case name of
                "Vector" -> do
                  let el_ty = tfvec_elem ty
                  elem_htype_either <- mkHTypeEither el_ty
                  case elem_htype_either of
                    -- Could create element type
                    Right elem_htype -> do
                      len <- tfp_to_int (tfvec_len_ty ty)
                      return $ Right $ VecType len elem_htype
                    -- Could not create element type
                    Left err -> return $ Left $ 
                      "\nVHDLTools.mkHTypeEither': Can not construct vectortype for elementtype: " ++ pprString el_ty ++ err
                "Unsigned" -> do
                  len <- tfp_to_int (sized_word_len_ty ty)
                  return $ Right $ SizedWType len
                "Signed" -> do
                  len <- tfp_to_int (sized_word_len_ty ty)
                  return $ Right $ SizedIType len
                "Index" -> do
                  bound <- tfp_to_int (ranged_word_bound_ty ty)
                  return $ Right $ RangedWType bound
                otherwise ->
                  mkTyConHType tycon args
    Nothing -> return $ Left $ "\nVHDLTools.mkHTypeEither': Do not know what to do with type: " ++ pprString ty

mkTyConHType :: TyCon.TyCon -> [Type.Type] -> TypeSession (Either String HType)
mkTyConHType tycon args =
  case TyCon.tyConDataCons tycon of
    -- Not an algebraic type
    [] -> return $ Left $ "VHDLTools.mkTyConHType: Only custom algebraic types are supported: " ++ pprString tycon
    [dc] -> do
      let arg_tys = DataCon.dataConRepArgTys dc
      let real_arg_tys = map (CoreSubst.substTy subst) arg_tys
      let real_arg_tys_nostate = filter (\x -> not (isStateType x)) real_arg_tys
      elem_htys_either <- mapM mkHTypeEither real_arg_tys_nostate
      case Either.partitionEithers elem_htys_either of
        ([], [elem_hty]) ->
          return $ Right elem_hty
        -- No errors in element types
        ([], elem_htys) ->
          return $ Right $ AggrType (nameToString (TyCon.tyConName tycon)) elem_htys
        -- There were errors in element types
        (errors, _) -> return $ Left $
          "\nVHDLTools.mkTyConHType: Can not construct type for: " ++ pprString tycon ++ "\n because no type can be construced for some of the arguments.\n"
          ++ (concat errors)
    dcs -> do
      let arg_tys = concatMap DataCon.dataConRepArgTys dcs
      let real_arg_tys = map (CoreSubst.substTy subst) arg_tys
      case real_arg_tys of
        [] ->
          return $ Right $ EnumType (nameToString (TyCon.tyConName tycon)) (map (nameToString . DataCon.dataConName) dcs)
        xs -> return $ Left $
          "VHDLTools.mkTyConHType: Only enum-like constructor datatypes supported: " ++ pprString dcs ++ "\n"
  where
    tyvars = TyCon.tyConTyVars tycon
    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst (zip tyvars args)

-- Translate a Haskell type to a VHDL type, generating a new type if needed.
-- Returns an error value, using the given message, when no type could be
-- created. Returns Nothing when the type is valid, but empty.
vhdlTy :: (TypedThing t, Outputable.Outputable t) => 
  String -> t -> TypeSession (Maybe AST.TypeMark)
vhdlTy msg ty = do
  htype <- mkHType msg ty
  vhdlTyMaybe htype

vhdlTyMaybe :: HType -> TypeSession (Maybe AST.TypeMark)
vhdlTyMaybe htype = do
  typemap <- MonadState.get tsTypes
  -- If not a builtin type, try the custom types
  let existing_ty = Map.lookup htype typemap
  case existing_ty of
    -- Found a type, return it
    Just (Just (t, _)) -> return $ Just t
    Just (Nothing) -> return Nothing
    -- No type yet, try to construct it
    Nothing -> do
      newty <- (construct_vhdl_ty htype)
      MonadState.modify tsTypes (Map.insert htype newty)
      case newty of
        Just (ty_id, ty_def) -> do
          MonadState.modify tsTypeDecls (\typedefs -> typedefs ++ [mktydecl (ty_id, ty_def)])
          return $ Just ty_id
        Nothing -> return Nothing

-- Construct a new VHDL type for the given Haskell type. Returns an error
-- message or the resulting typemark and typedef.
construct_vhdl_ty :: HType -> TypeSession TypeMapRec
-- State types don't generate VHDL
construct_vhdl_ty htype =
    case htype of
      StateType -> return  Nothing
      (SizedWType w) -> mkUnsignedTy w
      (SizedIType i) -> mkSignedTy i
      (RangedWType u) -> mkNaturalTy 0 u
      (VecType n e) -> mkVectorTy (VecType n e)
      -- Create a custom type from this tycon
      otherwise -> mkTyconTy htype

-- | Create VHDL type for a custom tycon
mkTyconTy :: HType -> TypeSession TypeMapRec
mkTyconTy htype =
  case htype of
    (AggrType tycon args) -> do
      elemTysMaybe <- mapM vhdlTyMaybe args
      case Maybe.catMaybes elemTysMaybe of
        [] -> -- No non-empty members
          return Nothing
        elem_tys -> do
          let elems = zipWith AST.ElementDec recordlabels elem_tys  
          let elem_names = concatMap prettyShow elem_tys
          let ty_id = mkVHDLExtId $ tycon ++ elem_names
          let ty_def = AST.TDR $ AST.RecordTypeDef elems
          let tupshow = mkTupleShow elem_tys ty_id
          MonadState.modify tsTypeFuns $ Map.insert (htype, showIdString) (showId, tupshow)
          return $ Just (ty_id, Just $ Left ty_def)
    (EnumType tycon dcs) -> do
      let elems = map mkVHDLExtId dcs
      let ty_id = mkVHDLExtId tycon
      let ty_def = AST.TDE $ AST.EnumTypeDef elems
      let enumShow = mkEnumShow elems ty_id
      MonadState.modify tsTypeFuns $ Map.insert (htype, showIdString) (showId, enumShow)
      return $ Just (ty_id, Just $ Left ty_def)
    otherwise -> error $ "\nVHDLTools.mkTyconTy: Called for HType that is neiter a AggrType or EnumType: " ++ show htype
  where
    -- Generate a bunch of labels for fields of a record
    recordlabels = map (\c -> mkVHDLBasicId [c]) ['A'..'Z']

-- | Create a VHDL vector type
mkVectorTy ::
  HType -- ^ The Haskell type of the Vector
  -> TypeSession TypeMapRec
      -- ^ An error message or The typemark created.

mkVectorTy (VecType len elHType) = do
  typesMap <- MonadState.get tsTypes
  elTyTmMaybe <- vhdlTyMaybe elHType
  case elTyTmMaybe of
    (Just elTyTm) -> do
      let ty_id = mkVHDLExtId $ "vector-"++ (AST.fromVHDLId elTyTm) ++ "-0_to_" ++ (show len)
      let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len - 1))]
      let existing_uvec_ty = fmap (fmap fst) $ Map.lookup (UVecType elHType) typesMap
      case existing_uvec_ty of
        Just (Just t) -> do
          let ty_def = AST.SubtypeIn t (Just range)
          return (Just (ty_id, Just $ Right ty_def))
        Nothing -> do
          let vec_id  = mkVHDLExtId $ "vector_" ++ (AST.fromVHDLId elTyTm)
          let vec_def = AST.TDA $ AST.UnconsArrayDef [tfvec_indexTM] elTyTm
          MonadState.modify tsTypes (Map.insert (UVecType elHType) (Just (vec_id, (Just $ Left vec_def))))
          MonadState.modify tsTypeDecls (\typedefs -> typedefs ++ [mktydecl (vec_id, (Just $ Left vec_def))])
          let vecShowFuns = mkVectorShow elTyTm vec_id
          mapM_ (\(id, subprog) -> MonadState.modify tsTypeFuns $ Map.insert (UVecType elHType, id) ((mkVHDLExtId id), subprog)) vecShowFuns
          let ty_def = AST.SubtypeIn vec_id (Just range)
          return (Just (ty_id, Just $ Right ty_def))
    -- Vector of empty elements becomes empty itself.
    Nothing -> return Nothing
mkVectorTy htype = error $ "\nVHDLTools.mkVectorTy: Called for HType that is not a VecType: " ++ show htype

mkNaturalTy ::
  Int -- ^ The minimum bound (> 0)
  -> Int -- ^ The maximum bound (> minimum bound)
  -> TypeSession TypeMapRec
      -- ^ An error message or The typemark created.
mkNaturalTy min_bound max_bound = do
  let bitsize = floor (logBase 2 (fromInteger (toInteger max_bound)))
  let ty_id = mkVHDLExtId $ "natural_" ++ (show min_bound) ++ "_to_" ++ (show max_bound)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit $ show min_bound) (AST.PrimLit $ show bitsize)]
  let ty_def = AST.SubtypeIn unsignedTM (Just range)
  return (Just (ty_id, Just $ Right ty_def))

mkUnsignedTy ::
  Int -- ^ Haskell type of the unsigned integer
  -> TypeSession TypeMapRec
mkUnsignedTy size = do
  let ty_id = mkVHDLExtId $ "unsigned_" ++ show (size - 1)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (size - 1))]
  let ty_def = AST.SubtypeIn unsignedTM (Just range)
  return (Just (ty_id, Just $ Right ty_def))
  
mkSignedTy ::
  Int -- ^ Haskell type of the signed integer
  -> TypeSession TypeMapRec
mkSignedTy size = do
  let ty_id = mkVHDLExtId $ "signed_" ++ show (size - 1)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (size - 1))]
  let ty_def = AST.SubtypeIn signedTM (Just range)
  return (Just (ty_id, Just $ Right ty_def))

-- Finds the field labels for VHDL type generated for the given Core type,
-- which must result in a record type.
getFieldLabels :: Type.Type -> TypeSession [AST.VHDLId]
getFieldLabels ty = do
  -- Ensure that the type is generated (but throw away it's VHDLId)
  let error_msg = "\nVHDLTools.getFieldLabels: Can not get field labels, because: " ++ pprString ty ++ "can not be generated." 
  vhdlTy error_msg ty
  -- Get the types map, lookup and unpack the VHDL TypeDef
  types <- MonadState.get tsTypes
  -- Assume the type for which we want labels is really translatable
  htype <- mkHType error_msg ty
  case Map.lookup htype types of
    Nothing -> error $ "\nVHDLTools.getFieldLabels: Type not found? This should not happen!\nLooking for type: " ++ (pprString ty) ++ "\nhtype: " ++ (show htype) 
    Just Nothing -> return [] -- The type is empty
    Just (Just (_, Just (Left (AST.TDR (AST.RecordTypeDef elems))))) -> return $ map (\(AST.ElementDec id _) -> id) elems
    Just (Just (_, Just vty)) -> error $ "\nVHDLTools.getFieldLabels: Type not a record type? This should not happen!\nLooking for type: " ++ pprString (ty) ++ "\nhtype: " ++ (show htype) ++ "\nFound type: " ++ (show vty)
    
mktydecl :: (AST.VHDLId, Maybe (Either AST.TypeDef AST.SubtypeIn)) -> Maybe AST.PackageDecItem
mytydecl (_, Nothing) = Nothing
mktydecl (ty_id, Just (Left ty_def)) = Just $ AST.PDITD $ AST.TypeDec ty_id ty_def
mktydecl (ty_id, Just (Right ty_def)) = Just $ AST.PDISD $ AST.SubtypeDec ty_id ty_def

mkTupleShow :: 
  [AST.TypeMark] -- ^ type of each tuple element
  -> AST.TypeMark -- ^ type of the tuple
  -> AST.SubProgBody
mkTupleShow elemTMs tupleTM = AST.SubProgBody showSpec [] [showExpr]
  where
    tupPar    = AST.unsafeVHDLBasicId "tup"
    showSpec  = AST.Function showId [AST.IfaceVarDec tupPar tupleTM] stringTM
    showExpr  = AST.ReturnSm (Just $
                  AST.PrimLit "'('" AST.:&: showMiddle AST.:&: AST.PrimLit "')'")
      where
        showMiddle = if null elemTMs then
            AST.PrimLit "''"
          else
            foldr1 (\e1 e2 -> e1 AST.:&: AST.PrimLit "','" AST.:&: e2) $
              map ((genExprFCall showId).
                    AST.PrimName .
                    AST.NSelected .
                    (AST.NSimple tupPar AST.:.:).
                    tupVHDLSuffix)
                  (take tupSize recordlabels)
    recordlabels = map (\c -> mkVHDLBasicId [c]) ['A'..'Z']
    tupSize = length elemTMs

mkEnumShow ::
  [AST.VHDLId]
  -> AST.TypeMark
  -> AST.SubProgBody
mkEnumShow elemIds enumTM = AST.SubProgBody showSpec [] [showExpr]
  where
    enumPar    = AST.unsafeVHDLBasicId "enum"
    showSpec  = AST.Function showId [AST.IfaceVarDec enumPar enumTM] stringTM
    showExpr  = AST.ReturnSm (Just $
                  AST.PrimLit (show $ tail $ init $ AST.fromVHDLId enumTM))

mkVectorShow ::
  AST.TypeMark -- ^ elemtype
  -> AST.TypeMark -- ^ vectype
  -> [(String,AST.SubProgBody)]
mkVectorShow elemTM vectorTM = 
  [ (headId, AST.SubProgBody headSpec []                   [headExpr])
  , (tailId, AST.SubProgBody tailSpec [AST.SPVD tailVar]   [tailExpr, tailRet])
  , (showIdString, AST.SubProgBody showSpec [AST.SPSB doShowDef] [showRet])
  ]
  where
    vecPar  = AST.unsafeVHDLBasicId "vec"
    resId   = AST.unsafeVHDLBasicId "res"
    headSpec = AST.Function (mkVHDLExtId headId) [AST.IfaceVarDec vecPar vectorTM] elemTM
    -- return vec(0);
    headExpr = AST.ReturnSm (Just (AST.PrimName $ AST.NIndexed (AST.IndexedName 
                    (AST.NSimple vecPar) [AST.PrimLit "0"])))
    vecSlice init last =  AST.PrimName (AST.NSlice 
                                      (AST.SliceName 
                                            (AST.NSimple vecPar) 
                                            (AST.ToRange init last)))
    tailSpec = AST.Function (mkVHDLExtId tailId) [AST.IfaceVarDec vecPar vectorTM] vectorTM
       -- variable res : fsvec_x (0 to vec'length-2); 
    tailVar = 
         AST.VarDec resId 
                (AST.SubtypeIn vectorTM
                  (Just $ AST.ConstraintIndex $ AST.IndexConstraint 
                   [AST.ToRange (AST.PrimLit "0")
                            (AST.PrimName (AST.NAttribute $ 
                              AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) AST.:-:
                                (AST.PrimLit "2"))   ]))
                Nothing       
       -- res AST.:= vec(1 to vec'length-1)
    tailExpr = AST.NSimple resId AST.:= (vecSlice 
                               (AST.PrimLit "1") 
                               (AST.PrimName (AST.NAttribute $ 
                                  AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing) 
                                                             AST.:-: AST.PrimLit "1"))
    tailRet = AST.ReturnSm (Just $ AST.PrimName $ AST.NSimple resId)
    showSpec  = AST.Function showId [AST.IfaceVarDec vecPar vectorTM] stringTM
    doShowId  = AST.unsafeVHDLExtId "doshow"
    doShowDef = AST.SubProgBody doShowSpec [] [doShowRet]
      where doShowSpec = AST.Function doShowId [AST.IfaceVarDec vecPar vectorTM] 
                                           stringTM
            -- case vec'len is
            --  when  0 => return "";
            --  when  1 => return head(vec);
            --  when others => return show(head(vec)) & ',' &
            --                        doshow (tail(vec));
            -- end case;
            doShowRet = 
              AST.CaseSm (AST.PrimName (AST.NAttribute $ 
                          AST.AttribName (AST.NSimple vecPar) (AST.NSimple $ mkVHDLBasicId lengthId) Nothing))
              [AST.CaseSmAlt [AST.ChoiceE $ AST.PrimLit "0"] 
                         [AST.ReturnSm (Just $ AST.PrimLit "\"\"")],
               AST.CaseSmAlt [AST.ChoiceE $ AST.PrimLit "1"] 
                         [AST.ReturnSm (Just $ 
                          genExprFCall showId 
                               (genExprFCall (mkVHDLExtId headId) (AST.PrimName $ AST.NSimple vecPar)) )],
               AST.CaseSmAlt [AST.Others] 
                         [AST.ReturnSm (Just $ 
                           genExprFCall showId 
                             (genExprFCall (mkVHDLExtId headId) (AST.PrimName $ AST.NSimple vecPar)) AST.:&:
                           AST.PrimLit "','" AST.:&:
                           genExprFCall doShowId 
                             (genExprFCall (mkVHDLExtId tailId) (AST.PrimName $ AST.NSimple vecPar)) ) ]]
    -- return '<' & doshow(vec) & '>';
    showRet =  AST.ReturnSm (Just $ AST.PrimLit "'<'" AST.:&:
                               genExprFCall doShowId (AST.PrimName $ AST.NSimple vecPar) AST.:&:
                               AST.PrimLit "'>'" )

mkBuiltInShow :: [AST.SubProgBody]
mkBuiltInShow = [ AST.SubProgBody showBitSpec [] [showBitExpr]
                , AST.SubProgBody showBoolSpec [] [showBoolExpr]
                , AST.SubProgBody showSingedSpec [] [showSignedExpr]
                , AST.SubProgBody showUnsignedSpec [] [showUnsignedExpr]
                -- , AST.SubProgBody showNaturalSpec [] [showNaturalExpr]
                ]
  where
    bitPar      = AST.unsafeVHDLBasicId "s"
    boolPar     = AST.unsafeVHDLBasicId "b"
    signedPar   = AST.unsafeVHDLBasicId "sint"
    unsignedPar = AST.unsafeVHDLBasicId "uint"
    -- naturalPar  = AST.unsafeVHDLBasicId "nat"
    showBitSpec = AST.Function showId [AST.IfaceVarDec bitPar std_logicTM] stringTM
    -- if s = '1' then return "'1'" else return "'0'"
    showBitExpr = AST.IfSm (AST.PrimName (AST.NSimple bitPar) AST.:=: AST.PrimLit "'1'")
                        [AST.ReturnSm (Just $ AST.PrimLit "\"High\"")]
                        []
                        (Just $ AST.Else [AST.ReturnSm (Just $ AST.PrimLit "\"Low\"")])
    showBoolSpec = AST.Function showId [AST.IfaceVarDec boolPar booleanTM] stringTM
    -- if b then return "True" else return "False"
    showBoolExpr = AST.IfSm (AST.PrimName (AST.NSimple boolPar))
                        [AST.ReturnSm (Just $ AST.PrimLit "\"True\"")]
                        []
                        (Just $ AST.Else [AST.ReturnSm (Just $ AST.PrimLit "\"False\"")])
    showSingedSpec = AST.Function showId [AST.IfaceVarDec signedPar signedTM] stringTM
    showSignedExpr =  AST.ReturnSm (Just $
                        AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerId) 
                        (AST.NIndexed $ AST.IndexedName (AST.NSimple imageId) [signToInt]) Nothing )
                      where
                        signToInt = genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple signedPar)
    showUnsignedSpec =  AST.Function showId [AST.IfaceVarDec unsignedPar unsignedTM] stringTM
    showUnsignedExpr =  AST.ReturnSm (Just $
                          AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerId) 
                          (AST.NIndexed $ AST.IndexedName (AST.NSimple imageId) [unsignToInt]) Nothing )
                        where
                          unsignToInt = genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple unsignedPar)
    -- showNaturalSpec = AST.Function showId [AST.IfaceVarDec naturalPar naturalTM] stringTM
    -- showNaturalExpr = AST.ReturnSm (Just $
    --                     AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerId)
    --                     (AST.NIndexed $ AST.IndexedName (AST.NSimple imageId) [AST.PrimName $ AST.NSimple $ naturalPar]) Nothing )
                      
  
genExprFCall :: AST.VHDLId -> AST.Expr -> AST.Expr
genExprFCall fName args = 
   AST.PrimFCall $ AST.FCall (AST.NSimple fName)  $
             map (\exp -> Nothing AST.:=>: AST.ADExpr exp) [args] 

genExprPCall2 :: AST.VHDLId -> AST.Expr -> AST.Expr -> AST.SeqSm             
genExprPCall2 entid arg1 arg2 =
        AST.ProcCall (AST.NSimple entid) $
         map (\exp -> Nothing AST.:=>: AST.ADExpr exp) [arg1,arg2]

mkSigDec :: CoreSyn.CoreBndr -> TranslatorSession (Maybe AST.SigDec)
mkSigDec bndr = do
  let error_msg = "\nVHDL.mkSigDec: Can not make signal declaration for type: \n" ++ pprString bndr 
  type_mark_maybe <- MonadState.lift tsType $ vhdlTy error_msg (Var.varType bndr)
  case type_mark_maybe of
    Just type_mark -> return $ Just (AST.SigDec (varToVHDLId bndr) type_mark Nothing)
    Nothing -> return Nothing

-- | Does the given thing have a non-empty type?
hasNonEmptyType :: (TypedThing t, Outputable.Outputable t) => 
  t -> TranslatorSession Bool
hasNonEmptyType thing = MonadState.lift tsType $ isJustM (vhdlTy "hasNonEmptyType: Non representable type?" thing)