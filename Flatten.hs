module Flatten where
import CoreSyn
import Control.Monad
import qualified Var
import qualified Type
import qualified Name
import qualified Maybe
import qualified Control.Arrow as Arrow
import qualified DataCon
import qualified CoreUtils
import qualified Data.Traversable as Traversable
import qualified Data.Foldable as Foldable
import Control.Applicative
import Outputable ( showSDoc, ppr )
import qualified Control.Monad.State as State

import HsValueMap
import TranslatorTypes
import FlattenTypes

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
  FlatFunction args res apps conds sigs''''
  where
    init_state        = ([], [], [], 0)
    (fres, end_state) = State.runState (flattenExpr [] expr) init_state
    (apps, conds, sigs, _)  = end_state
    (args, res)       = fres
    arg_ports         = concat (map Foldable.toList args)
    res_ports         = Foldable.toList res
    -- Mark args and result signals as input and output ports resp.
    sigs'             = fmap (markSignals SigPortIn arg_ports) sigs
    sigs''            = fmap (markSignals SigPortOut res_ports) sigs'
    -- Mark args and result states as old and new state resp.
    args_states       = concat $ zipWith stateList (hsFuncArgs hsfunc) args
    sigs'''           = foldl (\s (num, id) -> map (markSignal (SigStateOld num) id) s) sigs'' args_states
    res_states        = stateList (hsFuncRes hsfunc) res
    sigs''''          = foldl (\s (num, id) -> map (markSignal (SigStateNew num) id) s) sigs''' res_states

flattenExpr ::
  BindMap
  -> CoreExpr
  -> FlattenState ([SignalMap], SignalMap)

flattenExpr binds lam@(Lam b expr) = do
  -- Find the type of the binder
  let (arg_ty, _) = Type.splitFunTy (CoreUtils.exprType lam)
  -- Create signal names for the binder
  defs <- genSignals arg_ty
  let binds' = (b, Left defs):binds
  (args, res) <- flattenExpr binds' expr
  return (defs : args, res)

flattenExpr binds (Var id) =
  case bind of
    Left sig_use -> return ([], sig_use)
    Right _ -> error "Higher order functions not supported."
  where
    bind = Maybe.fromMaybe
      (error $ "Argument " ++ Name.getOccString id ++ "is unknown")
      (lookup id binds)

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
      flattenApplicationExpr binds (CoreUtils.exprType app) f args
  where
    flattenBuildTupleExpr binds args = do
      -- Flatten each of our args
      flat_args <- (State.mapM (flattenExpr binds) args)
      -- Check and split each of the arguments
      let (_, arg_ress) = unzip (zipWith checkArg args flat_args)
      let res = Tuple arg_ress
      return ([], res)

    -- | Flatten a normal application expression
    flattenApplicationExpr binds ty f args = do
      -- Find the function to call
      let func = appToHsFunction ty f args
      -- Flatten each of our args
      flat_args <- (State.mapM (flattenExpr binds) args)
      -- Check and split each of the arguments
      let (_, arg_ress) = unzip (zipWith checkArg args flat_args)
      -- Generate signals for our result
      res <- genSignals ty
      -- Create the function application
      let app = FApp {
        appFunc = func,
        appArgs = arg_ress,
        appRes  = res
      }
      addApp app
      return ([], res)
    -- | Check a flattened expression to see if it is valid to use as a
    --   function argument. The first argument is the original expression for
    --   use in the error message.
    checkArg arg flat =
      let (args, res) = flat in
      if not (null args)
        then error $ "Passing lambda expression or function as a function argument not supported: " ++ (showSDoc $ ppr arg)
        else flat 

flattenExpr binds l@(Let (NonRec b bexpr) expr) = do
  (b_args, b_res) <- flattenExpr binds bexpr
  if not (null b_args)
    then
      error $ "Higher order functions not supported in let expression: " ++ (showSDoc $ ppr l)
    else
      let binds' = (b, Left b_res) : binds in
      flattenExpr binds' expr

flattenExpr binds l@(Let (Rec _) _) = error $ "Recursive let definitions not supported: " ++ (showSDoc $ ppr l)

flattenExpr binds expr@(Case (Var v) b _ alts) =
  case alts of
    [alt] -> flattenSingleAltCaseExpr binds v b alt
    otherwise -> error $ "Multiple alternative case expression not supported: " ++ (showSDoc $ ppr expr)
  where
    flattenSingleAltCaseExpr ::
      BindMap
                                -- A list of bindings in effect
      -> Var.Var                -- The scrutinee
      -> CoreBndr               -- The binder to bind the scrutinee to
      -> CoreAlt                -- The single alternative
      -> FlattenState ( [SignalMap], SignalMap)
                                           -- See expandExpr
    flattenSingleAltCaseExpr binds v b alt@(DataAlt datacon, bind_vars, expr) =
      if not (DataCon.isTupleCon datacon) 
        then
          error $ "Dataconstructors other than tuple constructors not supported in case pattern of alternative: " ++ (showSDoc $ ppr alt)
        else
          let
            -- Lookup the scrutinee (which must be a variable bound to a tuple) in
            -- the existing bindings list and get the portname map for each of
            -- it's elements.
            Left (Tuple tuple_sigs) = Maybe.fromMaybe 
              (error $ "Case expression uses unknown scrutinee " ++ Name.getOccString v)
              (lookup v binds)
            -- TODO include b in the binds list
            -- Merge our existing binds with the new binds.
            binds' = (zip bind_vars (map Left tuple_sigs)) ++ binds 
          in
            -- Expand the expression with the new binds list
            flattenExpr binds' expr
    flattenSingleAltCaseExpr _ _ _ alt = error $ "Case patterns other than data constructors not supported in case alternative: " ++ (showSDoc $ ppr alt)


      
flattenExpr _ _ = do
  return ([], Tuple [])

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
  
-- | Returns pairs of signals that should be mapped to state in this function.
getOwnStates ::
  HsFunction                      -- | The function to look at
  -> FlatFunction                 -- | The function to look at
  -> [(StateId, SignalInfo, SignalInfo)]   
        -- | The state signals. The first is the state number, the second the
        --   signal to assign the current state to, the last is the signal
        --   that holds the new state.

getOwnStates hsfunc flatfunc =
  [(old_num, old_info, new_info) 
    | (old_num, old_info) <- args_states
    , (new_num, new_info) <- res_states
    , old_num == new_num]
  where
    sigs = flat_sigs flatfunc
    -- Translate args and res to lists of (statenum, sigid)
    args = concat $ zipWith stateList (hsFuncArgs hsfunc) (flat_args flatfunc)
    res = stateList (hsFuncRes hsfunc) (flat_res flatfunc)
    -- Replace the second tuple element with the corresponding SignalInfo
    args_states = map (Arrow.second $ signalInfo sigs) args
    res_states = map (Arrow.second $ signalInfo sigs) res

    
-- vim: set ts=8 sw=2 sts=2 expandtab:
