{-# LANGUAGE PatternGuards, TypeSynonymInstances #-}
-- | This module provides a number of functions to find out things about Core
-- programs. This module does not provide the actual plumbing to work with
-- Core and Haskell (it uses HsTools for this), but only the functions that
-- know about various libraries and know which functions to call.
module CLasH.Utils.Core.CoreTools where

--Standard modules
import qualified Maybe
import qualified List
import qualified System.IO.Unsafe
import qualified Data.Map as Map
import qualified Data.Accessor.Monad.Trans.StrictState as MonadState

-- GHC API
import qualified GHC
import qualified Type
import qualified TcType
import qualified HsExpr
import qualified HsTypes
import qualified HscTypes
import qualified Name
import qualified Id
import qualified TyCon
import qualified DataCon
import qualified TysWiredIn
import qualified DynFlags
import qualified SrcLoc
import qualified CoreSyn
import qualified Var
import qualified IdInfo
import qualified VarSet
import qualified CoreUtils
import qualified CoreFVs
import qualified Literal
import qualified MkCore
import qualified VarEnv
import qualified VarSet
import qualified Outputable
import qualified TypeRep

-- Local imports
import CLasH.Translator.TranslatorTypes
import CLasH.Utils.GhcTools
import CLasH.Utils.Core.BinderTools
import CLasH.Utils.HsTools
import CLasH.Utils.Pretty
import CLasH.Utils
import qualified CLasH.Utils.Core.BinderTools as BinderTools

-- | A single binding, used as a shortcut to simplify type signatures.
type Binding = (CoreSyn.CoreBndr, CoreSyn.CoreExpr)

-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int. Checks if the type really is a Dec type and
-- caches the results.
-- tfp_to_int :: Type.Type -> TypeSession Int
-- tfp_to_int ty = do
--   hscenv <- MonadState.get tsHscEnv
--   let norm_ty = normalize_tfp_int hscenv ty
--   case Type.splitTyConApp_maybe norm_ty of
--     Just (tycon, args) -> do
--       let name = Name.getOccString (TyCon.tyConName tycon)
--       case name of
--         "Dec" ->
--           tfp_to_int' ty
--         otherwise -> do
--           return $ error ("Callin tfp_to_int on non-dec:" ++ (show ty))
--     Nothing -> return $ error ("Callin tfp_to_int on non-dec:" ++ (show ty))
tfp_to_int :: Type.Type -> TypeSession Int
tfp_to_int ty = tfp_to_int' (show ty ++ "\n") ty

tfp_to_int' :: String -> Type.Type -> TypeSession Int
tfp_to_int' msg ty@(TypeRep.TyConApp tycon args) = if (TyCon.isClosedSynTyCon tycon) && (null args) then do
    lens <- MonadState.get tsTfpInts
    let knownSynonymMaybe = Map.lookup tycon lens
    case knownSynonymMaybe of
      Just knownSynonym -> return knownSynonym
      Nothing -> do
        let tycon' = TyCon.synTyConType tycon
        len <- tycon' `seq` tfp_to_int' (msg ++ " > " ++ (Name.getOccString (TyCon.tyConName tycon))) $! tycon'
        len `seq` MonadState.modify tsTfpInts $! (Map.insert tycon len)
        return len
  else if (TyCon.isClosedSynTyCon tycon) then do
    let tyconNameString = Name.getOccString (TyCon.tyConName tycon)
    case tyconNameString of
      "R:IfFalseyz" -> do
        let arg = args!!1
        len <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconNameString) $! arg
        return len
      -- TODO: Add more cases for type synonyms introduced by the Renamer
      -- FIXME: substitution of type variables by type arguments is potentially
      -- wrong!! Check if there are cases when this is valid. If not, throw an
      -- Error if we do not know the syntycon name! 
      _ -> do {
              ; let { ty'  = TyCon.synTyConType tycon
                    ; tyvarSet = VarSet.varSetElems $ Type.tyVarsOfType ty'
                    ; ty''  = let
                                tysubst = if length args == length tyvarSet then
                                    Type.zipTopTvSubst tyvarSet args
                                  else
                                    error $ "CoreTools.tfp_to_int': TyVars and Args don't match \nContext: " ++ msg
                              in
                                Type.substTy tysubst ty'
                    }            
              ; len <- (Type.seqType ty'') `seq` tfp_to_int' (msg ++ " > " ++ tyconNameString) $! ty''
              ; return len
              }
  else do
    let tyconName = pprString tycon
    let tyconNameString = Name.getOccString (TyCon.tyConName tycon)
    case tyconNameString of
      "Dec" -> do
        let arg = head args
        len <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        return len
      ":."  -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len  = int0 `seq` int1 `seq` int0 * 10 + int1
        return len
      "DecN" -> return 0
      "Dec0" -> return 0
      "Dec1" -> return 1
      "Dec2" -> return 2
      "Dec3" -> return 3
      "Dec4" -> return 4
      "Dec5" -> return 5
      "Dec6" -> return 6
      "Dec7" -> return 7
      "Dec8" -> return 8
      "Dec9" -> return 9
      "Succ" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let len = int `seq` int + 1
        return len
      "Pred" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let len = int `seq` int - 1
        return len
      ":+:" -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len  = int0 `seq` int1 `seq` int0 + int1
        return len
      ":-:" -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len  = int0 `seq` int1 `seq` int0 - int1
        return len
      ":*:" -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len  = int0 `seq` int1 `seq` int0 * int1
        return len
      "Pow2" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let len = int `seq` int * int
        return len
      "Mul2" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let len = int `seq` int + int
        return len
      "Div2" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let len = int `seq` int `div` 2
        return len
      "Fac" -> do
        let arg = head args
        int <- arg `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg
        let fac x = if x == 0 then 1 else x * fac (x - 1)
        let len = int `seq` fac int
        return len
      "Min" -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len = int0 `seq` int1 `seq` if int0 <= int1 then int0 else int1
        return len
      "Max" -> do
        let arg0 = head args
        let arg1 = args!!1
        int0 <- arg0 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg0
        int1 <- arg1 `seq` tfp_to_int' (msg ++ " > " ++ tyconName) $! arg1
        let len = int0 `seq` int1 `seq` if int0 >= int1 then int0 else int1
        return len
      _ -> error $ "CoreTools.tfp_to_int: Unknown TyCon : " ++ pprString tycon ++ "\n Context: " ++ msg
tfp_to_int' msg ty = error $ "CoreTools.tfp_to_int: Not a TyConApp: " ++ show ty ++ "\n Context: " ++ msg


-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int. Caches the results. Do not use directly, use
-- tfp_to_int instead.
-- tfp_to_int' :: Type.Type -> TypeSession Int
-- tfp_to_int' ty = do
--   lens <- MonadState.get tsTfpInts
--   hscenv <- MonadState.get tsHscEnv
--   let norm_ty = normalize_tfp_int hscenv ty
--   let existing_len = Map.lookup (OrdType norm_ty) lens
--   case existing_len of
--     Just len -> return len
--     Nothing -> do
--       let new_len = eval_tfp_int hscenv ty
--       MonadState.modify tsTfpInts (Map.insert (OrdType norm_ty) (new_len))
--       return new_len
      
-- | Evaluate a core Type representing type level int from the tfp
-- library to a real int. Do not use directly, use tfp_to_int instead.
eval_tfp_int :: HscTypes.HscEnv -> Type.Type -> Int
eval_tfp_int env ty =
  unsafeRunGhc libdir $ do
    GHC.setSession env
    -- Automatically import modules for any fully qualified identifiers
    setDynFlag DynFlags.Opt_ImplicitImportQualified

    let from_int_t_name = mkRdrName "Types.Data.Num.Ops" "fromIntegerT"
    let from_int_t = SrcLoc.noLoc $ HsExpr.HsVar from_int_t_name
    let undef = hsTypedUndef $ coreToHsType ty
    let app = SrcLoc.noLoc $ HsExpr.HsApp (from_int_t) (undef)
    let int_ty = SrcLoc.noLoc $ HsTypes.HsTyVar TysWiredIn.intTyCon_RDR
    let expr = HsExpr.ExprWithTySig app int_ty
    core <- toCore expr
    execCore core
  where
    libdir = DynFlags.topDir dynflags
    dynflags = HscTypes.hsc_dflags env

normalize_tfp_int :: HscTypes.HscEnv -> Type.Type -> Type.Type
normalize_tfp_int env ty =
   System.IO.Unsafe.unsafePerformIO $
     normalizeType env ty

sized_word_len_ty :: Type.Type -> Type.Type
sized_word_len_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.sized_word_len_ty: Not a sized word type: " ++ (pprString ty)
    [len]         = args

sized_int_len_ty :: Type.Type -> Type.Type
sized_int_len_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.sized_int_len_ty: Not a sized int type: " ++ (pprString ty)
    [len]         = args
    
ranged_word_bound_ty :: Type.Type -> Type.Type
ranged_word_bound_ty ty = len
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.ranged_word_bound_ty: Not a sized word type: " ++ (pprString ty)
    [len]         = args

tfvec_len_ty :: Type.Type -> Type.Type
tfvec_len_ty ty = len
  where  
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.tfvec_len_ty: Not a vector type: " ++ (pprString ty)
    [len, el_ty] = args
    
-- | Get the element type of a TFVec type
tfvec_elem :: Type.Type -> Type.Type
tfvec_elem ty = el_ty
  where
    args = case Type.splitTyConApp_maybe ty of
      Just (tycon, args) -> args
      Nothing -> error $ "\nCoreTools.tfvec_len: Not a vector type: " ++ (pprString ty)
    [len, el_ty] = args

-- | Gets the index of the given datacon in the given typed thing.
-- Errors out if it does not occur or if the type is not an ADT.
datacon_index :: TypedThing t => t -> DataCon.DataCon -> Int
datacon_index tt dc = case List.elemIndex dc dcs of
    Nothing -> error $ "Datacon " ++ pprString dc ++ " does not occur in typed thing: " ++ pprString tt
    Just i -> i
  where
    dcs = datacons_for tt

-- | Gets all datacons for the given typed thing. Errors out if the
-- typed thing is not ADT typed.
datacons_for :: TypedThing t => t -> [DataCon.DataCon]
datacons_for tt =
  case getType tt of
    Nothing -> error $ "Getting datacon index of untyped thing? " ++ pprString tt
    Just ty -> case Type.splitTyConApp_maybe ty of
      Nothing -> error $ "Trying to find datacon in a type without a tycon?" ++ pprString ty
      Just (tycon, _) -> case TyCon.tyConDataCons_maybe tycon of
        Nothing -> error $ "Trying to find datacon in a type without datacons?" ++ pprString ty
        Just dcs -> dcs

-- Is the given core expression a lambda abstraction?
is_lam :: CoreSyn.CoreExpr -> Bool
is_lam (CoreSyn.Lam _ _) = True
is_lam _ = False

-- Is the given core expression a let expression?
is_let :: CoreSyn.CoreExpr -> Bool
is_let (CoreSyn.Let _ _) = True
is_let _ = False

-- Is the given core expression of a function type?
is_fun :: CoreSyn.CoreExpr -> Bool
-- Treat Type arguments differently, because exprType is not defined for them.
is_fun (CoreSyn.Type _) = False
is_fun expr = (Type.isFunTy . CoreUtils.exprType) expr

-- Is the given core expression polymorphic (i.e., does it accept type
-- arguments?).
is_poly :: CoreSyn.CoreExpr -> Bool
-- Treat Type arguments differently, because exprType is not defined for them.
is_poly (CoreSyn.Type _) = False
is_poly expr = (Maybe.isJust . Type.splitForAllTy_maybe . CoreUtils.exprType) expr

-- Is the given core expression a variable reference?
is_var :: CoreSyn.CoreExpr -> Bool
is_var (CoreSyn.Var _) = True
is_var _ = False

is_lit :: CoreSyn.CoreExpr -> Bool
is_lit (CoreSyn.Lit _) = True
is_lit _ = False

-- Can the given core expression be applied to something? This is true for
-- applying to a value as well as a type.
is_applicable :: CoreSyn.CoreExpr -> Bool
is_applicable expr = is_fun expr || is_poly expr

-- Is the given core expression a variable or an application?
is_simple :: CoreSyn.CoreExpr -> Bool
is_simple (CoreSyn.App _ _) = True
is_simple (CoreSyn.Var _) = True
is_simple (CoreSyn.Cast expr _) = is_simple expr
is_simple _ = False

-- Does the given CoreExpr have any free type vars?
has_free_tyvars :: CoreSyn.CoreExpr -> Bool
has_free_tyvars = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars Var.isTyVar)

-- Does the given type have any free type vars?
ty_has_free_tyvars :: Type.Type -> Bool
ty_has_free_tyvars = not . VarSet.isEmptyVarSet . Type.tyVarsOfType

-- Does the given CoreExpr have any free local vars?
has_free_vars :: CoreSyn.CoreExpr -> Bool
has_free_vars = not . VarSet.isEmptyVarSet . CoreFVs.exprFreeVars

-- Does the given expression use any of the given binders?
expr_uses_binders :: [CoreSyn.CoreBndr] -> CoreSyn.CoreExpr -> Bool
expr_uses_binders bndrs = not . VarSet.isEmptyVarSet . (CoreFVs.exprSomeFreeVars (`elem` bndrs))

-- Turns a Var CoreExpr into the Id inside it. Will of course only work for
-- simple Var CoreExprs, not complexer ones.
exprToVar :: CoreSyn.CoreExpr -> Var.Id
exprToVar (CoreSyn.Var id) = id
exprToVar expr = error $ "\nCoreTools.exprToVar: Not a var: " ++ show expr

-- Turns a Lit CoreExpr into the Literal inside it.
exprToLit :: CoreSyn.CoreExpr -> Literal.Literal
exprToLit (CoreSyn.Lit lit) = lit
exprToLit expr = error $ "\nCoreTools.exprToLit: Not a lit: " ++ show expr

-- Removes all the type and dictionary arguments from the given argument list,
-- leaving only the normal value arguments. The type given is the type of the
-- expression applied to this argument list.
get_val_args :: Type.Type -> [CoreSyn.CoreExpr] -> [CoreSyn.CoreExpr]
get_val_args ty args = drop n args
  where
    (tyvars, predtypes, _) = TcType.tcSplitSigmaTy ty
    -- The first (length tyvars) arguments should be types, the next 
    -- (length predtypes) arguments should be dictionaries. We drop this many
    -- arguments, to get at the value arguments.
    n = length tyvars + length predtypes

-- Finds out what literal Integer this expression represents.
getIntegerLiteral :: CoreSyn.CoreExpr -> TranslatorSession Integer
getIntegerLiteral expr =
  case CoreSyn.collectArgs expr of
    (CoreSyn.Var f, [CoreSyn.Lit (Literal.MachInt integer)]) 
      | getFullString f == "GHC.Integer.smallInteger" -> return integer
      | getFullString f == "GHC.Types.I#" -> return integer
    (CoreSyn.Var f, [CoreSyn.Lit (Literal.MachInt64 integer)]) 
      | getFullString f == "GHC.Integer.int64ToInteger" -> return integer
    (CoreSyn.Var f, [CoreSyn.Lit (Literal.MachWord integer)]) 
      | getFullString f == "GHC.Integer.wordToInteger" -> return integer
    (CoreSyn.Var f, [CoreSyn.Lit (Literal.MachWord64 integer)]) 
      | getFullString f == "GHC.Integer.word64ToInteger" -> return integer
    -- fromIntegerT returns the integer corresponding to the type of its
    -- (third) argument. Since it is polymorphic, the type of that
    -- argument is passed as the first argument, so we can just use that
    -- one.
    (CoreSyn.Var f, [CoreSyn.Type dec_ty, dec_dict, CoreSyn.Type num_ty, num_dict, arg]) 
      | getFullString f == "Types.Data.Num.Ops.fromIntegerT" -> do
          int <- MonadState.lift tsType $ tfp_to_int dec_ty
          return $ toInteger int
    _ -> error $ "CoreTools.getIntegerLiteral: Unsupported Integer literal: " ++ pprString expr

reduceCoreListToHsList :: 
  [HscTypes.CoreModule] -- ^ The modules where parts of the list are hidden
  -> CoreSyn.CoreExpr   -- ^ The refence to atleast one of the nodes
  -> TranslatorSession [CoreSyn.CoreExpr]
reduceCoreListToHsList cores app@(CoreSyn.App _ _) = do {
  ; let { (fun, args) = CoreSyn.collectArgs app
        ; len         = length args 
        } ;
  ; case len of
      3 -> do {
        ; let topelem = args!!1
        ; case (args!!2) of
            (varz@(CoreSyn.Var id)) -> do {
              ; binds <- mapM (findExpr (isVarName id)) cores
              ; otherelems <- reduceCoreListToHsList cores (head (Maybe.catMaybes binds))
              ; return (topelem:otherelems)
              }
            (appz@(CoreSyn.App _ _)) -> do {
              ; otherelems <- reduceCoreListToHsList cores appz
              ; return (topelem:otherelems)
              }
            otherwise -> return [topelem]
        }
      otherwise -> return []
  }
  where
    isVarName :: Monad m => Var.Var -> Var.Var -> m Bool
    isVarName lookfor bind = return $ (Var.varName lookfor) == (Var.varName bind)

reduceCoreListToHsList _ _ = return []

-- Is the given var the State data constructor?
isStateCon :: Var.Var -> Bool
isStateCon var =
  -- See if it is a DataConWrapId (not DataConWorkId, since State is a
  -- newtype).
  case Id.idDetails var of
    IdInfo.DataConWrapId dc -> 
      -- See if the datacon is the State datacon from the State type.
      let tycon = DataCon.dataConTyCon dc
          tyname = Name.getOccString tycon
          dcname = Name.getOccString dc
      in case (tyname, dcname) of
        ("State", "State") -> True
        _ -> False
    _ -> False

-- | Is the given type a State type?
isStateType :: Type.Type -> Bool
-- Resolve any type synonyms remaining
isStateType ty | Just ty' <- Type.tcView ty = isStateType ty'
isStateType ty  = Maybe.isJust $ do
  -- Split the type. Don't use normal splitAppTy, since that looks through
  -- newtypes, and we want to see the State newtype.
  (typef, _) <- Type.repSplitAppTy_maybe ty
  -- See if the applied type is a type constructor
  (tycon, _) <- Type.splitTyConApp_maybe typef
  if TyCon.isNewTyCon tycon && Name.getOccString tycon == "State"
    then
      Just ()
    else
      Nothing

-- | Does the given TypedThing have a State type?
hasStateType :: (TypedThing t) => t -> Bool
hasStateType expr = case getType expr of
  Nothing -> False
  Just ty -> isStateType ty


-- | Flattens nested lets into a single list of bindings. The expression
--   passed does not have to be a let expression, if it isn't an empty list of
--   bindings is returned.
flattenLets ::
  CoreSyn.CoreExpr -- ^ The expression to flatten.
  -> ([Binding], CoreSyn.CoreExpr) -- ^ The bindings and resulting expression.
flattenLets (CoreSyn.Let binds expr) = 
  (bindings ++ bindings', expr')
  where
    -- Recursively flatten the contained expression
    (bindings', expr') =flattenLets expr
    -- Flatten our own bindings to remove the Rec / NonRec constructors
    bindings = CoreSyn.flattenBinds [binds]
flattenLets expr = ([], expr)

-- | Create bunch of nested non-recursive let expressions from the given
-- bindings. The first binding is bound at the highest level (and thus
-- available in all other bindings).
mkNonRecLets :: [Binding] -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr
mkNonRecLets bindings expr = MkCore.mkCoreLets binds expr
  where
    binds = map (uncurry CoreSyn.NonRec) bindings

-- | A class of things that (optionally) have a core Type. The type is
-- optional, since Type expressions don't have a type themselves.
class Outputable.Outputable t => TypedThing t where
  getType :: t -> Maybe Type.Type

instance TypedThing CoreSyn.CoreExpr where
  getType (CoreSyn.Type _) = Nothing
  getType expr = Just $ CoreUtils.exprType expr

instance TypedThing CoreSyn.CoreBndr where
  getType = return . Id.idType

instance TypedThing Type.Type where
  getType = return . id

-- | Generate new uniques for all binders in the given expression.
-- Does not support making type variables unique, though this could be
-- supported if required (by passing a CoreSubst.Subst instead of VarEnv to
-- genUniques' below).
genUniques :: CoreSyn.CoreExpr -> TranslatorSession CoreSyn.CoreExpr
genUniques = genUniques' VarEnv.emptyVarEnv

-- | A helper function to generate uniques, that takes a VarEnv containing the
--   substitutions already performed.
genUniques' :: VarEnv.VarEnv CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> TranslatorSession CoreSyn.CoreExpr
genUniques' subst (CoreSyn.Var f) = do
  -- Replace the binder with its new value, if applicable.
  let f' = VarEnv.lookupWithDefaultVarEnv subst f f
  return (CoreSyn.Var f')
-- Leave literals untouched
genUniques' subst (CoreSyn.Lit l) = return $ CoreSyn.Lit l
genUniques' subst (CoreSyn.App f arg) = do
  -- Only work on subexpressions
  f' <- genUniques' subst f
  arg' <- genUniques' subst arg
  return (CoreSyn.App f' arg')
-- Don't change type abstractions
genUniques' subst expr@(CoreSyn.Lam bndr res) | CoreSyn.isTyVar bndr = return expr
genUniques' subst (CoreSyn.Lam bndr res) = do
  -- Generate a new unique for the bound variable
  (subst', bndr') <- genUnique subst bndr
  res' <- genUniques' subst' res
  return (CoreSyn.Lam bndr' res')
genUniques' subst (CoreSyn.Let (CoreSyn.NonRec bndr bound) res) = do
  -- Make the binders unique
  (subst', bndr') <- genUnique subst bndr
  bound' <- genUniques' subst' bound
  res' <- genUniques' subst' res
  return $ CoreSyn.Let (CoreSyn.NonRec bndr' bound') res'
genUniques' subst (CoreSyn.Let (CoreSyn.Rec binds) res) = do
  -- Make each of the binders unique
  (subst', bndrs') <- mapAccumLM genUnique subst (map fst binds)
  bounds' <- mapM (genUniques' subst' . snd) binds
  res' <- genUniques' subst' res
  let binds' = zip bndrs' bounds'
  return $ CoreSyn.Let (CoreSyn.Rec binds') res'
genUniques' subst (CoreSyn.Case scrut bndr ty alts) = do
  -- Process the scrutinee with the original substitution, since non of the
  -- binders bound in the Case statement is in scope in the scrutinee.
  scrut' <- genUniques' subst scrut
  -- Generate a new binder for the scrutinee
  (subst', bndr') <- genUnique subst bndr
  -- Process each of the alts
  alts' <- mapM (doalt subst') alts
  return $ CoreSyn.Case scrut' bndr' ty alts'
  where
    doalt subst (con, bndrs, expr) = do
      (subst', bndrs') <- mapAccumLM genUnique subst bndrs
      expr' <- genUniques' subst' expr
      -- Note that we don't return subst', since bndrs are only in scope in
      -- expr.
      return (con, bndrs', expr')
genUniques' subst (CoreSyn.Cast expr coercion) = do
  expr' <- genUniques' subst expr
  -- Just process the casted expression
  return $ CoreSyn.Cast expr' coercion
genUniques' subst (CoreSyn.Note note expr) = do
  expr' <- genUniques' subst expr
  -- Just process the annotated expression
  return $ CoreSyn.Note note expr'
-- Leave types untouched
genUniques' subst expr@(CoreSyn.Type _) = return expr

-- Generate a new unique for the given binder, and extend the given
-- substitution to reflect this.
genUnique :: VarEnv.VarEnv CoreSyn.CoreBndr -> CoreSyn.CoreBndr -> TranslatorSession (VarEnv.VarEnv CoreSyn.CoreBndr, CoreSyn.CoreBndr)
genUnique subst bndr = do
  bndr' <- BinderTools.cloneVar bndr
  -- Replace all occurences of the old binder with a reference to the new
  -- binder.
  let subst' = VarEnv.extendVarEnv subst bndr bndr'
  return (subst', bndr')

-- Create a "selector" case that selects the ith field from dc_ith
-- datacon
mkSelCase :: CoreSyn.CoreExpr -> Int -> Int -> TranslatorSession CoreSyn.CoreExpr
mkSelCase scrut dc_i i = do
  case Type.splitTyConApp_maybe scrut_ty of
    -- The scrutinee should have a type constructor. We keep the type
    -- arguments around so we can instantiate the field types below
    Just (tycon, tyargs) -> case TyCon.tyConDataCons_maybe tycon of
      -- The scrutinee type should have a single dataconstructor,
      -- otherwise we can't construct a valid selector case.
      Just dcs | dc_i < 0 || dc_i >= length dcs -> error $ "\nCoreTools.mkSelCase: Creating extractor case, but datacon index is invalid." ++ error_msg
               | otherwise -> do
        let datacon = (dcs!!dc_i)
        let field_tys = DataCon.dataConInstOrigArgTys datacon  tyargs
        if i < 0 || i >= length field_tys
          then error $ "\nCoreTools.mkSelCase: Creating extractor case, but field index is invalid." ++ error_msg
          else do
            -- Create a list of wild binders for the fields we don't want
            let wildbndrs = map MkCore.mkWildBinder field_tys
            -- Create a single binder for the field we want
            sel_bndr <- mkInternalVar "sel" (field_tys!!i)
            -- Create a wild binder for the scrutinee
            let scrut_bndr = MkCore.mkWildBinder scrut_ty
            -- Create the case expression
            let binders = take i wildbndrs ++ [sel_bndr] ++ drop (i+1) wildbndrs
            return $ CoreSyn.Case scrut scrut_bndr scrut_ty [(CoreSyn.DataAlt datacon, binders, CoreSyn.Var sel_bndr)]
      Nothing -> error $ "CoreTools.mkSelCase: Creating extractor case, but scrutinee has no datacons?" ++ error_msg
    Nothing -> error $ "CoreTools.mkSelCase: Creating extractor case, but scrutinee has no tycon?" ++ error_msg
  where
    scrut_ty = CoreUtils.exprType scrut
    error_msg = " Extracting element " ++ (show i) ++ " from datacon " ++ (show dc_i) ++ " from '" ++ pprString scrut ++ "'" ++ " Type: " ++ (pprString scrut_ty)
