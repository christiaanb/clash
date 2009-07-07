module VHDLTools where

-- Standard modules
import qualified Maybe
import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Arrow as Arrow
import qualified Data.Monoid as Monoid
import Data.Accessor
import Debug.Trace

-- ForSyDe
import qualified ForSyDe.Backend.VHDL.AST as AST

-- GHC API
import CoreSyn
import qualified Name
import qualified OccName
import qualified Var
import qualified Id
import qualified TyCon
import qualified Type
import qualified DataCon
import qualified CoreSubst

-- Local imports
import VHDLTypes
import CoreTools
import Pretty
import Constants

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
      Left bndr -> AST.NSimple (varToVHDLId bndr)
      Right name -> name
    assign    = dst_name AST.:<==: (AST.ConWforms whenelse false_wform Nothing)
  in
    AST.CSSASm assign

mkAssocElems :: 
  [AST.Expr]                    -- | The argument that are applied to function
  -> AST.VHDLName               -- | The binder in which to store the result
  -> Entity                     -- | The entity to map against.
  -> [AST.AssocElem]            -- | The resulting port maps
mkAssocElems args res entity =
    -- Create the actual AssocElems
    zipWith mkAssocElem ports sigs
  where
    -- Turn the ports and signals from a map into a flat list. This works,
    -- since the maps must have an identical form by definition. TODO: Check
    -- the similar form?
    arg_ports = ent_args entity
    res_port  = ent_res entity
    -- Extract the id part from the (id, type) tuple
    ports     = map fst (res_port : arg_ports)
    -- Translate signal numbers into names
    sigs      = (vhdlNameToVHDLExpr res : args)

-- | Create an VHDL port -> signal association
mkAssocElem :: AST.VHDLId -> AST.Expr -> AST.AssocElem
mkAssocElem port signal = Just port AST.:=>: (AST.ADExpr signal) 

-- | Create an VHDL port -> signal association
mkAssocElemIndexed :: AST.VHDLId -> AST.VHDLId -> AST.VHDLId -> AST.AssocElem
mkAssocElemIndexed port signal index = Just port AST.:=>: (AST.ADName (AST.NIndexed (AST.IndexedName 
                      (AST.NSimple signal) [AST.PrimName $ AST.NSimple index])))

mkComponentInst ::
  String -- ^ The portmap label
  -> AST.VHDLId -- ^ The entity name
  -> [AST.AssocElem] -- ^ The port assignments
  -> AST.ConcSm
mkComponentInst label entity_id portassigns = AST.CSISm compins
  where
    -- We always have a clock port, so no need to map it anywhere but here
    clk_port = mkAssocElem (mkVHDLExtId "clk") (idToVHDLExpr $ mkVHDLExtId "clk")
    compins = AST.CompInsSm (mkVHDLExtId label) (AST.IUEntity (AST.NSimple entity_id)) (AST.PMapAspect (portassigns ++ [clk_port]))

-----------------------------------------------------------------------------
-- Functions to generate VHDL Exprs
-----------------------------------------------------------------------------

-- Turn a variable reference into a AST expression
varToVHDLExpr :: Var.Var -> AST.Expr
varToVHDLExpr var = 
  case Id.isDataConWorkId_maybe var of
    Just dc -> dataconToVHDLExpr dc
    -- This is a dataconstructor.
    -- Not a datacon, just another signal. Perhaps we should check for
    -- local/global here as well?
    -- Sadly so.. tfp decimals are types, not data constructors, but instances
    -- should still be translated to integer literals. It is probebly not the
    -- best solution to translate them here.
    -- FIXME: Find a better solution for translating instances of tfp integers
    Nothing -> 
        let 
          ty  = Var.varType var
          res = case Type.splitTyConApp_maybe ty of
                  Just (tycon, args) ->
                    case Name.getOccString (TyCon.tyConName tycon) of
                      "Dec" -> AST.PrimLit $ (show (eval_tfp_int ty))
                      otherwise -> AST.PrimName $ AST.NSimple $ varToVHDLId var
        in
          res

-- Turn a VHDLName into an AST expression
vhdlNameToVHDLExpr = AST.PrimName

-- Turn a VHDL Id into an AST expression
idToVHDLExpr = vhdlNameToVHDLExpr . AST.NSimple

-- Turn a Core expression into an AST expression
exprToVHDLExpr = varToVHDLExpr . exprToVar

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
varToVHDLId = mkVHDLExtId . varToString

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
    allowed = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9'] ++ " \"#&\\'()*+,./:;<=>_|!$%@?[]^`{}~-"
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
    ("Bit", std_logicTM),
    ("Bool", booleanTM), -- TysWiredIn.boolTy
    ("Dec", integerTM)
  ]

-- Translate a Haskell type to a VHDL type, generating a new type if needed.
-- Returns an error value, using the given message, when no type could be
-- created.
vhdl_ty :: String -> Type.Type -> TypeSession AST.TypeMark
vhdl_ty msg ty = do
  tm_either <- vhdl_ty_either ty
  case tm_either of
    Right tm -> return tm
    Left err -> error $ msg ++ "\n" ++ err

-- Translate a Haskell type to a VHDL type, generating a new type if needed.
-- Returns either an error message or the resulting type.
vhdl_ty_either :: Type.Type -> TypeSession (Either String AST.TypeMark)
vhdl_ty_either ty = do
  typemap <- getA vsTypes
  htype_either <- mkHType ty
  case htype_either of
    -- No errors
    Right htype -> do
      let builtin_ty = do -- See if this is a tycon and lookup its name
            (tycon, args) <- Type.splitTyConApp_maybe ty
            let name = Name.getOccString (TyCon.tyConName tycon)
            Map.lookup name builtin_types
      -- If not a builtin type, try the custom types
      let existing_ty = (fmap fst) $ Map.lookup htype typemap
      case Monoid.getFirst $ Monoid.mconcat (map Monoid.First [builtin_ty, existing_ty]) of
        -- Found a type, return it
        Just t -> return (Right t)
        -- No type yet, try to construct it
        Nothing -> do
          newty_maybe <- (construct_vhdl_ty ty)
          case newty_maybe of
            Right (ty_id, ty_def) -> do
              -- TODO: Check name uniqueness
              modA vsTypes (Map.insert htype (ty_id, ty_def))
              modA vsTypeDecls (\typedefs -> typedefs ++ [mktydecl (ty_id, ty_def)]) 
              return (Right ty_id)
            Left err -> return $ Left $
              "VHDLTools.vhdl_ty: Unsupported Haskell type: " ++ pprString ty ++ "\n"
              ++ err
    -- Error when constructing htype
    Left err -> return $ Left err 

-- Construct a new VHDL type for the given Haskell type. Returns an error
-- message or the resulting typemark and typedef.
construct_vhdl_ty :: Type.Type -> TypeSession (Either String (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn))
construct_vhdl_ty ty = do
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) -> do
      let name = Name.getOccString (TyCon.tyConName tycon)
      case name of
        "TFVec" -> mk_vector_ty ty
        "SizedWord" -> mk_unsigned_ty ty
        "RangedWord" -> mk_natural_ty 0 (ranged_word_bound ty)
        -- Create a custom type from this tycon
        otherwise -> mk_tycon_ty tycon args
    Nothing -> return (Left $ "VHDLTools.construct_vhdl_ty: Cannot create type for non-tycon type: " ++ pprString ty ++ "\n")

-- | Create VHDL type for a custom tycon
mk_tycon_ty :: TyCon.TyCon -> [Type.Type] -> TypeSession (Either String (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn))
mk_tycon_ty tycon args =
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
        ([], elem_tys) -> do
          let elems = zipWith AST.ElementDec recordlabels elem_tys
          -- For a single construct datatype, build a record with one field for
          -- each argument.
          -- TODO: Add argument type ids to this, to ensure uniqueness
          -- TODO: Special handling for tuples?
          let elem_names = concat $ map prettyShow elem_tys
          let ty_id = mkVHDLExtId $ nameToString (TyCon.tyConName tycon) ++ elem_names
          let ty_def = AST.TDR $ AST.RecordTypeDef elems
          return $ Right (ty_id, Left ty_def)
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
  -> TypeSession (Either String (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn))
      -- ^ An error message or The typemark created.

mk_vector_ty ty = do
  types_map <- getA vsTypes
  let (nvec_l, nvec_el) = Type.splitAppTy ty
  let (nvec, leng) = Type.splitAppTy nvec_l
  let vec_ty = Type.mkAppTy nvec nvec_el
  let len = tfvec_len ty
  let el_ty = tfvec_elem ty
  el_ty_tm_either <- vhdl_ty_either el_ty
  case el_ty_tm_either of
    -- Could create element type
    Right el_ty_tm -> do
      let ty_id = mkVHDLExtId $ "vector-"++ (AST.fromVHDLId el_ty_tm) ++ "-0_to_" ++ (show len)
      let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (len - 1))]
      let existing_elem_ty = (fmap fst) $ Map.lookup (StdType $ OrdType vec_ty) types_map
      case existing_elem_ty of
        Just t -> do
          let ty_def = AST.SubtypeIn t (Just range)
          return (Right (ty_id, Right ty_def))
        Nothing -> do
          let vec_id = mkVHDLExtId $ "vector_" ++ (AST.fromVHDLId el_ty_tm)
          let vec_def = AST.TDA $ AST.UnconsArrayDef [tfvec_indexTM] el_ty_tm
          modA vsTypes (Map.insert (StdType $ OrdType vec_ty) (vec_id, (Left vec_def)))
          modA vsTypeDecls (\typedefs -> typedefs ++ [mktydecl (vec_id, (Left vec_def))]) 
          let ty_def = AST.SubtypeIn vec_id (Just range)
          return (Right (ty_id, Right ty_def))
    -- Could not create element type
    Left err -> return $ Left $ 
      "VHDLTools.mk_vector_ty: Can not construct vectortype for elementtype: " ++ pprString el_ty  ++ "\n"
      ++ err

mk_natural_ty ::
  Int -- ^ The minimum bound (> 0)
  -> Int -- ^ The maximum bound (> minimum bound)
  -> TypeSession (Either String (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn))
      -- ^ An error message or The typemark created.
mk_natural_ty min_bound max_bound = do
  let ty_id = mkVHDLExtId $ "nat_" ++ (show min_bound) ++ "_to_" ++ (show max_bound)
  let range = AST.ConstraintRange $ AST.SubTypeRange (AST.PrimLit $ (show min_bound)) (AST.PrimLit $ (show max_bound))
  let ty_def = AST.SubtypeIn naturalTM (Just range)
  return (Right (ty_id, Right ty_def))

mk_unsigned_ty ::
  Type.Type -- ^ Haskell type of the signed integer
  -> TypeSession (Either String (AST.TypeMark, Either AST.TypeDef AST.SubtypeIn))
mk_unsigned_ty ty = do
  let size  = sized_word_len ty
  let ty_id = mkVHDLExtId $ "unsigned_" ++ show (size - 1)
  let range = AST.ConstraintIndex $ AST.IndexConstraint [AST.ToRange (AST.PrimLit "0") (AST.PrimLit $ show (size - 1))]
  let ty_def = AST.SubtypeIn signedTM (Just range)
  return (Right (ty_id, Right ty_def))

-- Finds the field labels for VHDL type generated for the given Core type,
-- which must result in a record type.
getFieldLabels :: Type.Type -> TypeSession [AST.VHDLId]
getFieldLabels ty = do
  -- Ensure that the type is generated (but throw away it's VHDLId)
  let error_msg = "\nVHDLTools.getFieldLabels: Can not get field labels, because: " ++ pprString ty ++ "can not be generated." 
  vhdl_ty error_msg ty
  -- Get the types map, lookup and unpack the VHDL TypeDef
  types <- getA vsTypes
  -- Assume the type for which we want labels is really translatable
  Right htype <- mkHType ty
  case Map.lookup htype types of
    Just (_, Left (AST.TDR (AST.RecordTypeDef elems))) -> return $ map (\(AST.ElementDec id _) -> id) elems
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
                  len <- vec_len ty
                  return $ Right $ VecType len elem_htype
                -- Could not create element type
                Left err -> return $ Left $ 
                  "VHDLTools.mkHType: Can not construct vectortype for elementtype: " ++ pprString el_ty  ++ "\n"
                  ++ err
            "SizedWord" -> return $ Right $ StdType $ OrdType ty
            "RangedWord" -> return $ Right $ StdType $ OrdType ty
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

vec_len :: Type.Type -> TypeSession Int
vec_len ty = do
  veclens <- getA vsTfpInts
  let len_ty = tfvec_len_ty ty
  let existing_len = Map.lookup (OrdType len_ty) veclens
  case existing_len of
    Just len -> return len
    Nothing -> do
      let new_len = tfvec_len ty
      modA vsTfpInts (Map.insert (OrdType len_ty) (new_len))
      return new_len