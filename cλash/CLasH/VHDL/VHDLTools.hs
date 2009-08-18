{-# LANGUAGE RelaxedPolyRec #-} -- Needed for vhdl_ty_either', for some reason...
module CLasH.VHDL.VHDLTools where

-- Standard modules
import qualified Maybe
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Char as Char
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Arrow as Arrow
import qualified Control.Monad.Trans.State as State
import qualified Data.Monoid as Monoid
import Data.Accessor
import Data.Accessor.MonadState as MonadState
import Debug.Trace

-- ForSyDe
import qualified Language.VHDL.AST as AST

-- GHC API
import CoreSyn
import qualified Name
import qualified OccName
import qualified Var
import qualified Id
import qualified IdInfo
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
  Either CoreBndr AST.VHDLName -- ^ The signal to assign to
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
varToVHDLExpr var = do
  case Id.isDataConWorkId_maybe var of
    Just dc -> return $ dataconToVHDLExpr dc
    -- This is a dataconstructor.
    -- Not a datacon, just another signal. Perhaps we should check for
    -- local/global here as well?
    -- Sadly so.. tfp decimals are types, not data constructors, but instances
    -- should still be translated to integer literals. It is probebly not the
    -- best solution to translate them here.
    -- FIXME: Find a better solution for translating instances of tfp integers
    Nothing -> do
        let ty  = Var.varType var
        case Type.splitTyConApp_maybe ty of
                Just (tycon, args) ->
                  case Name.getOccString (TyCon.tyConName tycon) of
                    "Dec" -> do
                      len <- tfp_to_int ty
                      return $ AST.PrimLit $ (show len)
                    otherwise -> return $ AST.PrimName $ AST.NSimple $ varToVHDLId var

-- Turn a VHDLName into an AST expression
vhdlNameToVHDLExpr = AST.PrimName

-- Turn a VHDL Id into an AST expression
idToVHDLExpr = vhdlNameToVHDLExpr . AST.NSimple

-- Turn a Core expression into an AST expression
exprToVHDLExpr core = varToVHDLExpr (exprToVar core)

-- Turn a alternative constructor into an AST expression. For
-- dataconstructors, this is only the constructor itself, not any arguments it
-- has. Should not be called with a DEFAULT constructor.
altconToVHDLExpr :: CoreSyn.AltCon -> AST.Expr
altconToVHDLExpr (DataAlt dc) = dataconToVHDLExpr dc

altconToVHDLExpr (LitAlt _) = error "\nVHDL.conToVHDLExpr: Literals not support in case alternatives yet"
altconToVHDLExpr DEFAULT = error "\nVHDL.conToVHDLExpr: DEFAULT alternative should not occur here!"

-- Turn a datacon (without arguments!) into a VHDL expression.
dataconToVHDLExpr :: DataCon.DataCon -> AST.Expr
dataconToVHDLExpr dc = AST.PrimLit lit
  where
    tycon = DataCon.dataConTyCon dc
    tyname = TyCon.tyConName tycon
    dcname = DataCon.dataConName dc
    lit = case Name.getOccString tyname of
      -- TODO: Do something more robust than string matching
      "Bit"      -> case Name.getOccString dcname of "High" -> "'1'"; "Low" -> "'0'"
      "Bool" -> case Name.getOccString dcname of "True" -> "true"; "False" -> "false"

-----------------------------------------------------------------------------
-- Functions dealing with names, variables and ids
-----------------------------------------------------------------------------

-- Creates a VHDL Id from a binder
varToVHDLId ::
  CoreSyn.CoreBndr
  -> AST.VHDLId
varToVHDLId var = mkVHDLExtId $ (varToString var ++ varToStringUniq var ++ (show $ lowers $ varToStringUniq var))
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

-- | Maps the string name (OccName) of a type to the corresponding VHDL type,
-- for a few builtin types.
builtin_types = 
  Map.fromList [
    ("Bit", Just std_logicTM),
    ("Bool", Just booleanTM), -- TysWiredIn.boolTy
    ("Dec", Just integerTM)
  ]

-- Translate a Haskell type to a VHDL type, generating a new type if needed.
-- Returns an error value, using the given message, when no type could be
-- created. Returns Nothing when the type is valid, but empty.
vhdl_ty :: (TypedThing t, Outputable.Outputable t) => 
  String -> t -> TypeSession (Maybe AST.TypeMark)
vhdl_ty msg ty = do
  tm_either <- vhdl_ty_either ty
  case tm_either of
    Right tm -> return tm
    Left err -> error $ msg ++ "\n" ++ err

-- Translate a Haskell type to a VHDL type, generating a new type if needed.
-- Returns either an error message or the resulting type.
vhdl_ty_either :: (TypedThing t, Outputable.Outputable t) => 
  t -> TypeSession (Either String (Maybe AST.TypeMark))
vhdl_ty_either tything =
  case getType tything of
    Nothing -> return $ Left $ "VHDLTools.vhdl_ty: Typed thing without a type: " ++ pprString tything
    Just ty -> vhdl_ty_either' ty

vhdl_ty_either' :: Type.Type -> TypeSession (Either String (Maybe AST.TypeMark))
vhdl_ty_either' ty = do
  typemap <- getA tsTypes
  htype_either <- mkHType ty
  case htype_either of
    -- No errors
    Right htype -> do
      let builtin_ty = do -- See if this is a tycon and lookup its name
            (tycon, args) <- Type.splitTyConApp_maybe ty
            let name = Name.getOccString (TyCon.tyConName tycon)
            Map.lookup name builtin_types
      -- If not a builtin type, try the custom types
      let existing_ty = (Monad.liftM $ fmap fst) $ Map.lookup htype typemap
      case Monoid.getFirst $ Monoid.mconcat (map Monoid.First [builtin_ty, existing_ty]) of
        -- Found a type, return it
        Just t -> return (Right t)
        -- No type yet, try to construct it
        Nothing -> do
          newty_either <- (construct_vhdl_ty ty)
          case newty_either of
            Right newty  -> do
              -- TODO: Check name uniqueness
              modA tsTypes (Map.insert htype newty)
              case newty of
                Just (ty_id, ty_def) -> do
                  modA tsTypeDecls (\typedefs -> typedefs ++ [mktydecl (ty_id, ty_def)])
                  return (Right $ Just ty_id)
                Nothing -> return $ Right Nothing
            Left err -> return $ Left $
              "VHDLTools.vhdl_ty: Unsupported Haskell type: " ++ pprString ty ++ "\n"
              ++ err
    -- Error when constructing htype
    Left err -> return $ Left err 

-- Construct a new VHDL type for the given Haskell type. Returns an error
-- message or the resulting typemark and typedef.
construct_vhdl_ty :: Type.Type -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
-- State types don't generate VHDL
construct_vhdl_ty ty | isStateType ty = return $ Right Nothing
construct_vhdl_ty ty = do
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tycon)
      case name of
        "TFVec" -> mk_vector_ty ty
        "SizedWord" -> mk_unsigned_ty ty
        "SizedInt"  -> mk_signed_ty ty
        "RangedWord" -> do 
          bound <- tfp_to_int (ranged_word_bound_ty ty)
          mk_natural_ty 0 bound
        -- Create a custom type from this tycon
        otherwise -> mk_tycon_ty ty tycon args
    Nothing -> return (Left $ "VHDLTools.construct_vhdl_ty: Cannot create type for non-tycon type: " ++ pprString ty ++ "\n")

-- | Create VHDL type for a custom tycon
mk_tycon_ty :: Type.Type -> TyCon.TyCon -> [Type.Type] -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
mk_tycon_ty ty tycon args =
  case TyCon.tyConDataCons tycon of
    -- Not an algebraic type
    [] -> return (Left $ "VHDLTools.mk_tycon_ty: Only custom algebraic types are supported: " ++ pprString tycon ++ "\n")
    [dc] -> do
      let arg_tys = DataCon.dataConRepArgTys dc
      -- TODO: CoreSubst docs say each Subs can be applied only once. Is this a
      -- violation? Or does it only mean not to apply it again to the same
      -- subject?
      let real_arg_tys = map (CoreSubst.substTy subst) arg_tys
      elem_tys_either <- mapM vhdl_ty_either real_arg_tys
      case Either.partitionEithers elem_tys_either of
        -- No errors in element types
        ([], elem_tys') -> do
          -- Throw away all empty members
          case Maybe.catMaybes elem_tys' of
            [] -> -- No non-empty members
              return $ Right Nothing
            elem_tys -> do
              let elems = zipWith AST.ElementDec recordlabels elem_tys
              -- For a single construct datatype, build a record with one field for
              -- each argument.
              -- TODO: Add argument type ids to this, to ensure uniqueness
              -- TODO: Special handling for tuples?
              let elem_names = concat $ map prettyShow elem_tys
              let ty_id = mkVHDLExtId $ nameToString (TyCon.tyConName tycon) ++ elem_names
              let ty_def = AST.TDR $ AST.RecordTypeDef elems
              let tupshow = mkTupleShow elem_tys ty_id
              modA tsTypeFuns $ Map.insert (OrdType ty, showIdString) (showId, tupshow)
              return $ Right $ Just (ty_id, Left ty_def)
        -- There were errors in element types
        (errors, _) -> return $ Left $
          "VHDLTools.mk_tycon_ty: Can not construct type for: " ++ pprString tycon ++ "\n because no type can be construced for some of the arguments.\n"
          ++ (concat errors)
    dcs -> return $ Left $ "VHDLTools.mk_tycon_ty: Only single constructor datatypes supported: " ++ pprString tycon ++ "\n"
  where
    -- Create a subst that instantiates all types passed to the tycon
    -- TODO: I'm not 100% sure that this is the right way to do this. It seems
    -- to work so far, though..
    tyvars = TyCon.tyConTyVars tycon
    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst (zip tyvars args)
    -- Generate a bunch of labels for fields of a record
    recordlabels = map (\c -> mkVHDLBasicId [c]) ['A'..'Z']

-- | Create a VHDL vector type
mk_vector_ty ::
  Type.Type -- ^ The Haskell type of the Vector
  -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
      -- ^ An error message or The typemark created.

mk_vector_ty ty = do
  types_map <- getA tsTypes
  env <- getA tsHscEnv
  let (nvec_l, nvec_el) = Type.splitAppTy ty
  let (nvec, leng) = Type.splitAppTy nvec_l
  let vec_ty = Type.mkAppTy nvec nvec_el
  len <- tfp_to_int (tfvec_len_ty ty)
  let el_ty = tfvec_elem ty
  el_ty_tm_either <- vhdl_ty_either el_ty
  case el_ty_tm_either of
    -- Could create element type
    Right (Just el_ty_tm) -> do
      let ty_id = mkVHDLExtId $ "vector-"++ (AST.fromVHDLId el_ty_tm) ++ "-0_to_" ++ (show len)
      let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len - 1))]
      let existing_elem_ty = (fmap $ fmap fst) $ Map.lookup (StdType $ OrdType vec_ty) types_map
      case existing_elem_ty of
        Just (Just t) -> do
          let ty_def = AST.SubtypeIn t (Just range)
          return (Right $ Just (ty_id, Right ty_def))
        Nothing -> do
          let vec_id = mkVHDLExtId $ "vector_" ++ (AST.fromVHDLId el_ty_tm)
          let vec_def = AST.TDA $ AST.UnconsArrayDef [tfvec_indexTM] el_ty_tm
          modA tsTypes (Map.insert (StdType $ OrdType vec_ty) (Just (vec_id, (Left vec_def))))
          modA tsTypeDecls (\typedefs -> typedefs ++ [mktydecl (vec_id, (Left vec_def))])
          let vecShowFuns = mkVectorShow el_ty_tm vec_id
          mapM_ (\(id, subprog) -> modA tsTypeFuns $ Map.insert (OrdType vec_ty, id) ((mkVHDLExtId id), subprog)) vecShowFuns
          let ty_def = AST.SubtypeIn vec_id (Just range)
          return (Right $ Just (ty_id, Right ty_def))
    -- Empty element type? Empty vector type then. TODO: Does this make sense?
    -- Probably needs changes in the builtin functions as well...
    Right Nothing -> return $ Right Nothing
    -- Could not create element type
    Left err -> return $ Left $ 
      "VHDLTools.mk_vector_ty: Can not construct vectortype for elementtype: " ++ pprString el_ty  ++ "\n"
      ++ err

mk_natural_ty ::
  Int -- ^ The minimum bound (> 0)
  -> Int -- ^ The maximum bound (> minimum bound)
  -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
      -- ^ An error message or The typemark created.
mk_natural_ty min_bound max_bound = do
  let bitsize = floor (logBase 2 (fromInteger (toInteger max_bound)))
  let ty_id = mkVHDLExtId $ "natural_" ++ (show min_bound) ++ "_to_" ++ (show max_bound)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit $ show min_bound) (AST.PrimLit $ show bitsize)]
  let ty_def = AST.SubtypeIn unsignedTM (Just range)
  return (Right $ Just (ty_id, Right ty_def))

mk_unsigned_ty ::
  Type.Type -- ^ Haskell type of the unsigned integer
  -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
mk_unsigned_ty ty = do
  size <- tfp_to_int (sized_word_len_ty ty)
  let ty_id = mkVHDLExtId $ "unsigned_" ++ show (size - 1)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (size - 1))]
  let ty_def = AST.SubtypeIn unsignedTM (Just range)
  return (Right $ Just (ty_id, Right ty_def))
  
mk_signed_ty ::
  Type.Type -- ^ Haskell type of the signed integer
  -> TypeSession (Either String (Maybe (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn)))
mk_signed_ty ty = do
  size <- tfp_to_int (sized_int_len_ty ty)
  let ty_id = mkVHDLExtId $ "signed_" ++ show (size - 1)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (size - 1))]
  let ty_def = AST.SubtypeIn signedTM (Just range)
  return (Right $ Just (ty_id, Right ty_def))

-- Finds the field labels for VHDL type generated for the given Core type,
-- which must result in a record type.
getFieldLabels :: Type.Type -> TypeSession [AST.VHDLId]
getFieldLabels ty = do
  -- Ensure that the type is generated (but throw away it's VHDLId)
  let error_msg = "\nVHDLTools.getFieldLabels: Can not get field labels, because: " ++ pprString ty ++ "can not be generated." 
  vhdl_ty error_msg ty
  -- Get the types map, lookup and unpack the VHDL TypeDef
  types <- getA tsTypes
  -- Assume the type for which we want labels is really translatable
  Right htype <- mkHType ty
  case Map.lookup htype types of
    Just (Just (_, Left (AST.TDR (AST.RecordTypeDef elems)))) -> return $ map (\(AST.ElementDec id _) -> id) elems
    Just Nothing -> return [] -- The type is empty
    _ -> error $ "\nVHDL.getFieldLabels: Type not found or not a record type? This should not happen! Type: " ++ (show ty)
    
mktydecl :: (AST.VHDLId, Either AST.TypeDef AST.SubtypeIn) -> AST.PackageDecItem
mktydecl (ty_id, Left ty_def) = AST.PDITD $ AST.TypeDec ty_id ty_def
mktydecl (ty_id, Right ty_def) = AST.PDISD $ AST.SubtypeDec ty_id ty_def

mkHType :: Type.Type -> TypeSession (Either String HType)
mkHType ty = do
  -- FIXME: Do we really need to do this here again?
  let builtin_ty = do -- See if this is a tycon and lookup its name
        (tycon, args) <- Type.splitTyConApp_maybe ty
        let name = Name.getOccString (TyCon.tyConName tycon)
        Map.lookup name builtin_types
  case builtin_ty of
    Just typ ->
      return $ Right $ BuiltinType $ prettyShow typ
    Nothing ->
      case Type.splitTyConApp_maybe ty of
        Just (tycon, args) -> do
          let name = Name.getOccString (TyCon.tyConName tycon)
          case name of
            "TFVec" -> do
              let el_ty = tfvec_elem ty
              elem_htype_either <- mkHType el_ty
              case elem_htype_either of
                -- Could create element type
                Right elem_htype -> do
                  len <- tfp_to_int (tfvec_len_ty ty)
                  return $ Right $ VecType len elem_htype
                -- Could not create element type
                Left err -> return $ Left $ 
                  "VHDLTools.mkHType: Can not construct vectortype for elementtype: " ++ pprString el_ty  ++ "\n"
                  ++ err
            "SizedWord" -> do
              len <- tfp_to_int (sized_word_len_ty ty)
              return $ Right $ SizedWType len
            "SizedInt" -> do
              len <- tfp_to_int (sized_word_len_ty ty)
              return $ Right $ SizedIType len
            "RangedWord" -> do
              bound <- tfp_to_int (ranged_word_bound_ty ty)
              return $ Right $ RangedWType bound
            otherwise -> do
              mkTyConHType tycon args
        Nothing -> return $ Right $ StdType $ OrdType ty

-- FIXME: Do we really need to do this here again?
mkTyConHType :: TyCon.TyCon -> [Type.Type] -> TypeSession (Either String HType)
mkTyConHType tycon args =
  case TyCon.tyConDataCons tycon of
    -- Not an algebraic type
    [] -> return $ Left $ "VHDLTools.mkHType: Only custom algebraic types are supported: " ++ pprString tycon ++ "\n"
    [dc] -> do
      let arg_tys = DataCon.dataConRepArgTys dc
      let real_arg_tys = map (CoreSubst.substTy subst) arg_tys
      elem_htys_either <- mapM mkHType real_arg_tys
      case Either.partitionEithers elem_htys_either of
        -- No errors in element types
        ([], elem_htys) -> do
          return $ Right $ ADTType (nameToString (TyCon.tyConName tycon)) elem_htys
        -- There were errors in element types
        (errors, _) -> return $ Left $
          "VHDLTools.mkHType: Can not construct type for: " ++ pprString tycon ++ "\n because no type can be construced for some of the arguments.\n"
          ++ (concat errors)
    dcs -> return $ Left $ "VHDLTools.mkHType: Only single constructor datatypes supported: " ++ pprString tycon ++ "\n"
  where
    tyvars = TyCon.tyConTyVars tycon
    subst = CoreSubst.extendTvSubstList CoreSubst.emptySubst (zip tyvars args)

-- Is the given type representable at runtime?
isReprType :: Type.Type -> TypeSession Bool
isReprType ty = do
  ty_either <- vhdl_ty_either ty
  return $ case ty_either of
    Left _ -> False
    Right _ -> True


tfp_to_int :: Type.Type -> TypeSession Int
tfp_to_int ty = do
  hscenv <- getA tsHscEnv
  let norm_ty = normalise_tfp_int hscenv ty
  case Type.splitTyConApp_maybe norm_ty of
    Just (tycon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tycon)
      case name of
        "Dec" -> do
          len <- tfp_to_int' ty
          return len
        otherwise -> do
          modA tsTfpInts (Map.insert (OrdType norm_ty) (-1))
          return $ error ("Callin tfp_to_int on non-dec:" ++ (show ty))
    Nothing -> return $ error ("Callin tfp_to_int on non-dec:" ++ (show ty))

tfp_to_int' :: Type.Type -> TypeSession Int
tfp_to_int' ty = do
  lens <- getA tsTfpInts
  hscenv <- getA tsHscEnv
  let norm_ty = normalise_tfp_int hscenv ty
  let existing_len = Map.lookup (OrdType norm_ty) lens
  case existing_len of
    Just len -> return len
    Nothing -> do
      let new_len = eval_tfp_int hscenv ty
      modA tsTfpInts (Map.insert (OrdType norm_ty) (new_len))
      return new_len
      
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
    headExpr = AST.ReturnSm (Just $ (AST.PrimName $ AST.NIndexed (AST.IndexedName 
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
                        signToInt = genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple $ signedPar)
    showUnsignedSpec =  AST.Function showId [AST.IfaceVarDec unsignedPar unsignedTM] stringTM
    showUnsignedExpr =  AST.ReturnSm (Just $
                          AST.PrimName $ AST.NAttribute $ AST.AttribName (AST.NSimple integerId) 
                          (AST.NIndexed $ AST.IndexedName (AST.NSimple imageId) [unsignToInt]) Nothing )
                        where
                          unsignToInt = genExprFCall (mkVHDLBasicId toIntegerId) (AST.PrimName $ AST.NSimple $ unsignedPar)
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
  type_mark_maybe <- MonadState.lift tsType $ vhdl_ty error_msg (Var.varType bndr)
  case type_mark_maybe of
    Just type_mark -> return $ Just (AST.SigDec (varToVHDLId bndr) type_mark Nothing)
    Nothing -> return Nothing

-- | Does the given thing have a non-empty type?
hasNonEmptyType :: (TypedThing t, Outputable.Outputable t) => 
  t -> TranslatorSession Bool
hasNonEmptyType thing = MonadState.lift tsType $ isJustM (vhdl_ty "hasNonEmptyType: Non representable type?" thing)
