module Flatten where
import CoreSyn
import qualified Control.Monad as Monad
import qualified Var
import qualified Type
import qualified Name
import qualified Maybe
import qualified Control.Arrow as Arrow
import qualified DataCon
import qualified TyCon
import qualified Literal
import qualified CoreUtils
import qualified TysWiredIn
import qualified IdInfo
import qualified Data.Traversable as Traversable
import qualified Data.Foldable as Foldable
import Control.Applicative
import Outputable ( showSDoc, ppr )
import qualified Control.Monad.Trans.State as State

import HsValueMap
import TranslatorTypes
import FlattenTypes
import CoreTools

-- Extract the arguments from a data constructor application (that is, the
-- normal args, leaving out the type args).
dataConAppArgs :: DataCon.DataCon -> [CoreExpr] -> [CoreExpr]
dataConAppArgs dc args =
    drop tycount args
  where
    tycount = length $ DataCon.dataConAllTyVars dc

genSignals ::
  Type.Type
  -> FlattenState SignalMap

genSignals ty =
  -- First generate a map with the right structure containing the types, and
  -- generate signals for each of them.
  Traversable.mapM (\ty -> genSignalId SigInternal ty) (mkHsValueMap ty)

-- | Marks a signal as the given SigUse, if its id is in the list of id's
--   given.
markSignals :: SigUse -> [SignalId] -> (SignalId, SignalInfo) -> (SignalId, SignalInfo)
markSignals use ids (id, info) =
  (id, info')
  where
    info' = if id `elem` ids then info { sigUse = use} else info

markSignal :: SigUse -> SignalId -> (SignalId, SignalInfo) -> (SignalId, SignalInfo)
markSignal use id = markSignals use [id]

-- | Flatten a haskell function
flattenFunction ::
  HsFunction                      -- ^ The function to flatten
  -> CoreBind                     -- ^ The function value
  -> FlatFunction                 -- ^ The resulting flat function

flattenFunction _ (Rec _) = error "Recursive binders not supported"
flattenFunction hsfunc bind@(NonRec var expr) =
  FlatFunction args res defs sigs
  where
    init_state        = ([], [], 0)
    (fres, end_state) = State.runState (flattenTopExpr hsfunc expr) init_state
    (defs, sigs, _)   = end_state
    (args, res)       = fres

flattenTopExpr ::
  HsFunction
  -> CoreExpr
  -> FlattenState ([SignalMap], SignalMap)

flattenTopExpr hsfunc expr = do
  -- Flatten the expression
  (args, res) <- flattenExpr [] expr
  
  -- Join the signal ids and uses together
  let zipped_args = zipWith zipValueMaps args (hsFuncArgs hsfunc)
  let zipped_res = zipValueMaps res (hsFuncRes hsfunc)
  -- Set the signal uses for each argument / result, possibly updating
  -- argument or result signals.
  args' <- mapM (Traversable.mapM $ hsUseToSigUse args_use) zipped_args
  res' <- Traversable.mapM (hsUseToSigUse res_use) zipped_res
  return (args', res')
  where
    args_use Port = SigPortIn
    args_use (State n) = SigStateOld n
    res_use Port = SigPortOut
    res_use (State n) = SigStateNew n


hsUseToSigUse :: 
  (HsValueUse -> SigUse)      -- ^ A function to actually map the use value
  -> (SignalId, HsValueUse)   -- ^ The signal to look at and its use
  -> FlattenState SignalId    -- ^ The resulting signal. This is probably the
                              --   same as the input, but it could be different.
hsUseToSigUse f (id, use) = do
  info <- getSignalInfo id
  id' <- case sigUse info of 
    -- Internal signals can be marked as different uses freely.
    SigInternal -> do
      return id
    -- Signals that already have another use, must be duplicated before
    -- marking. This prevents signals mapping to the same input or output
    -- port or state variables and ports overlapping, etc.
    otherwise -> do
      duplicateSignal id
  setSignalInfo id' (info { sigUse = f use})
  return id'

-- | Creates a new internal signal with the same type as the given signal
copySignal :: SignalId -> FlattenState SignalId
copySignal id = do
  -- Find the type of the original signal
  info <- getSignalInfo id
  let ty = sigTy info
  -- Generate a new signal (which is SigInternal for now, that will be
  -- sorted out later on).
  genSignalId SigInternal ty

-- | Duplicate the given signal, assigning its value to the new signal.
--   Returns the new signal id.
duplicateSignal :: SignalId -> FlattenState SignalId
duplicateSignal id = do
  -- Create a new signal
  id' <- copySignal id
  -- Assign the old signal to the new signal
  addDef $ UncondDef (Left id) id'
  -- Replace the signal with the new signal
  return id'
        
flattenExpr ::
  BindMap
  -> CoreExpr
  -> FlattenState ([SignalMap], SignalMap)

flattenExpr binds lam@(Lam b expr) = do
  -- Find the type of the binder
  let (arg_ty, _) = Type.splitFunTy (CoreUtils.exprType lam)
  -- Create signal names for the binder
  defs <- genSignals arg_ty
  -- Add name hints to the generated signals
  let binder_name = Name.getOccString b
  Traversable.mapM (addNameHint binder_name) defs
  let binds' = (b, Left defs):binds
  (args, res) <- flattenExpr binds' expr
  return (defs : args, res)

flattenExpr binds var@(Var id) =
  case Var.globalIdVarDetails id of
    IdInfo.NotGlobalId ->
      let 
        bind = Maybe.fromMaybe
          (error $ "Local value " ++ Name.getOccString id ++ " is unknown")
          (lookup id binds) 
      in
        case bind of
          Left sig_use -> return ([], sig_use)
          Right _ -> error "Higher order functions not supported."
    IdInfo.DataConWorkId datacon -> do
      if DataCon.isTupleCon datacon && (null $ DataCon.dataConAllTyVars datacon)
        then do
          -- Empty tuple construction
          return ([], Tuple [])
        else do
          lit <- dataConToLiteral datacon
          let ty = CoreUtils.exprType var
          sig_id <- genSignalId SigInternal ty
          -- Add a name hint to the signal
          addNameHint (Name.getOccString id) sig_id
          addDef (UncondDef (Right $ Literal lit Nothing) sig_id)
          return ([], Single sig_id)
    IdInfo.VanillaGlobal ->
      -- Treat references to globals as an application with zero elements
      flattenApplicationExpr binds (CoreUtils.exprType var) id []
    otherwise ->
      error $ "Ids other than local vars and dataconstructors not supported: " ++ (showSDoc $ ppr id)

flattenExpr binds app@(App _ _) = do
  -- Is this a data constructor application?
  case CoreUtils.exprIsConApp_maybe app of
    -- Is this a tuple construction?
    Just (dc, args) -> if DataCon.isTupleCon dc 
      then
        flattenBuildTupleExpr binds (dataConAppArgs dc args)
      else
        error $ "Data constructors other than tuples not supported: " ++ (showSDoc $ ppr app)
    otherwise ->
      -- Normal function application
      let ((Var f), args) = collectArgs app in
      let fname = Name.getOccString f in
      if fname == "fst" || fname == "snd" then do
        (args', Tuple [a, b]) <- flattenExpr binds (last args)
        return (args', if fname == "fst" then a else b)
      else if fname == "patError" then do
        -- This is essentially don't care, since the program will error out
        -- here. We'll just define undriven signals here.
        let (argtys, resty) = Type.splitFunTys $ CoreUtils.exprType app
        args <- mapM genSignals argtys
        res <- genSignals resty
        mapM (Traversable.mapM (addNameHint "NC")) args
        Traversable.mapM (addNameHint "NC") res
        return (args, res)
      else if fname == "==" then do
        -- Flatten the last two arguments (this skips the type arguments)
        ([], a) <- flattenExpr binds (last $ init args)
        ([], b) <- flattenExpr binds (last args)
        res <- mkEqComparisons a b
        return ([], res)
      else if fname == "fromInteger" then do
        let [to_ty, to_dict, val] = args 
        -- We assume this is an application of the GHC.Integer.smallInteger
        -- function to a literal
        let App smallint (Lit lit) = val
        let (Literal.MachInt int) = lit
        let ty = CoreUtils.exprType app
        sig_id <- genSignalId SigInternal ty
        -- TODO: fromInteger is defined for more types than just SizedWord
        let len = sized_word_len ty
        -- TODO: to_stdlogicvector doesn't work here, since SizedWord
        -- translates to a different type...
        addDef $ UncondDef (Right $ Literal ("to_stdlogicvector(to_unsigned(" ++ (show int) ++ ", " ++ (show len) ++ "))") Nothing) sig_id
        return ([], Single sig_id)
      else
        flattenApplicationExpr binds (CoreUtils.exprType app) f args
  where
    mkEqComparisons :: SignalMap -> SignalMap -> FlattenState SignalMap
    mkEqComparisons a b = do
      let zipped = zipValueMaps a b
      Traversable.mapM mkEqComparison zipped

    mkEqComparison :: (SignalId, SignalId) -> FlattenState SignalId
    mkEqComparison (a, b) = do
      -- Generate a signal to hold our result
      res <- genSignalId SigInternal TysWiredIn.boolTy
      -- Add a name hint to the signal
      addNameHint ("s" ++ show a ++ "_eq_s" ++ show b) res
      addDef (UncondDef (Right $ Eq a b) res)
      return res

    flattenBuildTupleExpr binds args = do
      -- Flatten each of our args
      flat_args <- (mapM (flattenExpr binds) args)
      -- Check and split each of the arguments
      let (_, arg_ress) = unzip (zipWith checkArg args flat_args)
      let res = Tuple arg_ress
      return ([], res)

flattenExpr binds l@(Let (NonRec b bexpr) expr) = do
  (b_args, b_res) <- flattenExpr binds bexpr
  if not (null b_args)
    then
      error $ "Higher order functions not supported in let expression: " ++ (showSDoc $ ppr l)
    else do
      let binds' = (b, Left b_res) : binds
      -- Add name hints to the generated signals
      let binder_name = Name.getOccString b
      Traversable.mapM (addNameHint binder_name) b_res
      flattenExpr binds' expr

flattenExpr binds l@(Let (Rec _) _) = error $ "Recursive let definitions not supported: " ++ (showSDoc $ ppr l)

flattenExpr binds expr@(Case scrut b _ alts) = do
  -- TODO: Special casing for higher order functions
  -- Flatten the scrutinee
  (_, res) <- flattenExpr binds scrut
  case alts of
    -- TODO include b in the binds list
    [alt] -> flattenSingleAltCaseExpr binds res b alt
    -- Reverse the alternatives, so the __DEFAULT alternative ends up last
    otherwise -> flattenMultipleAltCaseExpr binds res b (reverse alts)
  where
    flattenSingleAltCaseExpr ::
      BindMap
                                -- A list of bindings in effect
      -> SignalMap              -- The scrutinee
      -> CoreBndr               -- The binder to bind the scrutinee to
      -> CoreAlt                -- The single alternative
      -> FlattenState ( [SignalMap], SignalMap) -- See expandExpr

    flattenSingleAltCaseExpr binds scrut b alt@(DataAlt datacon, bind_vars, expr) =
      if DataCon.isTupleCon datacon
        then do
          -- Unpack the scrutinee (which must be a variable bound to a tuple) in
          -- the existing bindings list and get the portname map for each of
          -- it's elements.
          let Tuple tuple_sigs = scrut
          -- Add name hints to the returned signals
          let binder_name = Name.getOccString b
          Monad.zipWithM (\name  sigs -> Traversable.mapM (addNameHint $ Name.getOccString name) sigs) bind_vars tuple_sigs
          -- Merge our existing binds with the new binds.
          let binds' = (zip bind_vars (map Left tuple_sigs)) ++ binds 
          -- Expand the expression with the new binds list
          flattenExpr binds' expr
        else
          if null bind_vars
            then
              -- DataAlts without arguments don't need processing
              -- (flattenMultipleAltCaseExpr will have done this already).
              flattenExpr binds expr
            else
              error $ "Dataconstructors other than tuple constructors cannot have binder arguments in case pattern of alternative: " ++ (showSDoc $ ppr alt)

    flattenSingleAltCaseExpr binds _ _ alt@(DEFAULT, [], expr) =
      flattenExpr binds expr
      
    flattenSingleAltCaseExpr _ _ _ alt = error $ "Case patterns other than data constructors not supported in case alternative: " ++ (showSDoc $ ppr alt)

    flattenMultipleAltCaseExpr ::
      BindMap
                                -- A list of bindings in effect
      -> SignalMap              -- The scrutinee
      -> CoreBndr               -- The binder to bind the scrutinee to
      -> [CoreAlt]              -- The alternatives
      -> FlattenState ( [SignalMap], SignalMap) -- See expandExpr

    flattenMultipleAltCaseExpr binds scrut b (a:a':alts) = do
      (args, res) <- flattenSingleAltCaseExpr binds scrut b a
      (args', res') <- flattenMultipleAltCaseExpr binds scrut b (a':alts)
      case a of
        (DataAlt datacon, bind_vars, expr) -> do
          lit <- dataConToLiteral datacon
          -- The scrutinee must be a single signal
          let Single sig = scrut
          -- Create a signal that contains a boolean
          boolsigid <- genSignalId SigInternal TysWiredIn.boolTy
          addNameHint ("s" ++ show sig ++ "_eq_" ++ lit) boolsigid
          let expr = EqLit sig lit
          addDef (UncondDef (Right expr) boolsigid)
          -- Create conditional assignments of either args/res or
          -- args'/res based on boolsigid, and return the result.
          -- TODO: It seems this adds the name hint twice?
          our_args <- Monad.zipWithM (mkConditionals boolsigid) args args'
          our_res  <- mkConditionals boolsigid res res'
          return (our_args, our_res)
        otherwise ->
          error $ "Case patterns other than data constructors not supported in case alternative: " ++ (showSDoc $ ppr a)
      where
        -- Select either the first or second signal map depending on the value
        -- of the first argument (True == first map, False == second map)
        mkConditionals :: SignalId -> SignalMap -> SignalMap -> FlattenState SignalMap
        mkConditionals boolsigid true false = do
          let zipped = zipValueMaps true false
          Traversable.mapM (mkConditional boolsigid) zipped

        mkConditional :: SignalId -> (SignalId, SignalId) -> FlattenState SignalId
        mkConditional boolsigid (true, false) = do
          -- Create a new signal (true and false should be identically typed,
          -- so it doesn't matter which one we copy).
          res <- copySignal true
          addDef (CondDef boolsigid true false res)
          return res

    flattenMultipleAltCaseExpr binds scrut b (a:alts) =
      flattenSingleAltCaseExpr binds scrut b a

flattenExpr _ expr = do
  error $ "Unsupported expression: " ++ (showSDoc $ ppr expr)

-- | Flatten a normal application expression
flattenApplicationExpr binds ty f args = do
  -- Find the function to call
  let func = appToHsFunction ty f args
  -- Flatten each of our args
  flat_args <- (mapM (flattenExpr binds) args)
  -- Check and split each of the arguments
  let (_, arg_ress) = unzip (zipWith checkArg args flat_args)
  -- Generate signals for our result
  res <- genSignals ty
  -- Add name hints to the generated signals
  let resname = Name.getOccString f ++ "_res"
  Traversable.mapM (addNameHint resname) res
  -- Create the function application
  let app = FApp {
    appFunc = func,
    appArgs = arg_ress,
    appRes  = res
  }
  addDef app
  return ([], res)
-- | Check a flattened expression to see if it is valid to use as a
--   function argument. The first argument is the original expression for
--   use in the error message.
checkArg arg flat =
  let (args, res) = flat in
  if not (null args)
    then error $ "Passing lambda expression or function as a function argument not supported: " ++ (showSDoc $ ppr arg)
    else flat 

-- | Translates a dataconstructor without arguments to the corresponding
--   literal.
dataConToLiteral :: DataCon.DataCon -> FlattenState String
dataConToLiteral datacon = do
  let tycon = DataCon.dataConTyCon datacon
  let tyname = TyCon.tyConName tycon
  case Name.getOccString tyname of
    -- TODO: Do something more robust than string matching
    "Bit"      -> do
      let dcname = DataCon.dataConName datacon
      let lit = case Name.getOccString dcname of "High" -> "'1'"; "Low" -> "'0'"
      return lit
    "Bool" -> do
      let dcname = DataCon.dataConName datacon
      let lit = case Name.getOccString dcname of "True" -> "true"; "False" -> "false"
      return lit
    otherwise ->
      error $ "Literals of type " ++ (Name.getOccString tyname) ++ " not supported."

appToHsFunction ::
  Type.Type       -- ^ The return type
  -> Var.Var      -- ^ The function to call
  -> [CoreExpr]   -- ^ The function arguments
  -> HsFunction   -- ^ The needed HsFunction

appToHsFunction ty f args =
  HsFunction hsname hsargs hsres
  where
    hsname = Name.getOccString f
    hsargs = map (useAsPort . mkHsValueMap . CoreUtils.exprType) args
    hsres  = useAsPort (mkHsValueMap ty)

-- | Filters non-state signals and returns the state number and signal id for
--   state values.
filterState ::
  SignalId                       -- | The signal id to look at
  -> HsValueUse                  -- | How is this signal used?
  -> Maybe (StateId, SignalId )  -- | The state num and signal id, if this
                                 --   signal was used as state

filterState id (State num) = 
  Just (num, id)
filterState _ _ = Nothing

-- | Returns a list of the state number and signal id of all used-as-state
--   signals in the given maps.
stateList ::
  HsUseMap
  -> (SignalMap)
  -> [(StateId, SignalId)]

stateList uses signals =
    Maybe.catMaybes $ Foldable.toList $ zipValueMapsWith filterState signals uses
  
-- vim: set ts=8 sw=2 sts=2 expandtab:
