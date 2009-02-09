module Flatten where
import CoreSyn
import qualified Type
import qualified Name
import qualified TyCon
import qualified Maybe
import qualified CoreUtils
import qualified Control.Monad.State as State

-- | A datatype that maps each of the single values in a haskell structure to
-- a mapto. The map has the same structure as the haskell type mapped, ie
-- nested tuples etc.
data HsValueMap mapto =
  Tuple [HsValueMap mapto]
  | Single mapto
  deriving (Show, Eq)



-- | Creates a HsValueMap with the same structure as the given type, using the
--   given function for mapping the single types.
mkHsValueMap ::
  Type.Type                         -- ^ The type to map to a HsValueMap
  -> HsValueMap Type.Type           -- ^ The resulting map and state

mkHsValueMap ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) ->
      if (TyCon.isTupleTyCon tycon) 
        then
          Tuple (map mkHsValueMap args)
        else
          Single ty
    Nothing -> Single ty

data FlatFunction = FlatFunction {
  args   :: [SignalDefMap],
  res    :: SignalUseMap,
  --sigs   :: [SignalDef],
  apps   :: [App],
  conds  :: [CondDef]
} deriving (Show, Eq)
    
type SignalUseMap = HsValueMap SignalUse
type SignalDefMap = HsValueMap SignalDef

useMapToDefMap :: SignalUseMap -> SignalDefMap
useMapToDefMap (Single (SignalUse u)) = Single (SignalDef u)
useMapToDefMap (Tuple uses) = Tuple (map useMapToDefMap uses)

type SignalId = Int
data SignalUse = SignalUse {
  sigUseId :: SignalId
} deriving (Show, Eq)

data SignalDef = SignalDef {
  sigDefId :: SignalId
} deriving (Show, Eq)

data App = App {
  appFunc :: HsFunction,
  appArgs :: [SignalUseMap],
  appRes  :: SignalDefMap
} deriving (Show, Eq)

data CondDef = CondDef {
  cond    :: SignalUse,
  high    :: SignalUse,
  low     :: SignalUse,
  condRes :: SignalDef
} deriving (Show, Eq)

-- | How is a given (single) value in a function's type (ie, argument or
-- return value) used?
data HsValueUse = 
  Port           -- ^ Use it as a port (input or output)
  | State Int    -- ^ Use it as state (input or output). The int is used to
                 --   match input state to output state.
  | HighOrder {  -- ^ Use it as a high order function input
    hoName :: String,  -- ^ Which function is passed in?
    hoArgs :: [HsUseMap]   -- ^ Which arguments are already applied? This
                         -- ^ map should only contain Port and other
                         --   HighOrder values. 
  }
  deriving (Show, Eq)

type HsUseMap = HsValueMap HsValueUse

data HsFunction = HsFunction {
  hsFuncName :: String,
  hsFuncArgs :: [HsUseMap],
  hsFuncRes  :: HsUseMap
} deriving (Show, Eq)

type BindMap = [(
  CoreBndr,            -- ^ The bind name
  Either               -- ^ The bind value which is either
    SignalUseMap       -- ^ a signal
    (
      HsValueUse,      -- ^ or a HighOrder function
      [SignalUse]      -- ^ With these signals already applied to it
    )
  )]

type FlattenState = State.State ([App], [CondDef], SignalId)

-- | Add an application to the current FlattenState
addApp :: App -> FlattenState ()
addApp a = do
  (apps, conds, n) <- State.get
  State.put (a:apps, conds, n)

-- | Add a conditional definition to the current FlattenState
addCondDef :: CondDef -> FlattenState ()
addCondDef c = do
  (apps, conds, n) <- State.get
  State.put (apps, c:conds, n)

-- | Generates a new signal id, which is unique within the current flattening.
genSignalId :: FlattenState SignalId 
genSignalId = do
  (apps, conds, n) <- State.get
  State.put (apps, conds, n+1)
  return n

genSignalUses ::
  Type.Type
  -> FlattenState SignalUseMap

genSignalUses ty = do
  typeMapToUseMap tymap
  where
    -- First generate a map with the right structure containing the types
    tymap = mkHsValueMap ty

typeMapToUseMap ::
  HsValueMap Type.Type
  -> FlattenState SignalUseMap

typeMapToUseMap (Single ty) = do
  id <- genSignalId
  return $ Single (SignalUse id)

typeMapToUseMap (Tuple tymaps) = do
  usemaps <- mapM typeMapToUseMap tymaps
  return $ Tuple usemaps

-- | Flatten a haskell function
flattenFunction ::
  HsFunction                      -- ^ The function to flatten
  -> CoreBind                     -- ^ The function value
  -> FlatFunction                 -- ^ The resulting flat function

flattenFunction _ (Rec _) = error "Recursive binders not supported"
flattenFunction hsfunc bind@(NonRec var expr) =
  FlatFunction args res apps conds
  where
    init_state        = ([], [], 0)
    (fres, end_state) = State.runState (flattenExpr [] expr) init_state
    (args, res)       = fres
    (apps, conds, _)  = end_state

flattenExpr ::
  BindMap
  -> CoreExpr
  -> FlattenState ([SignalDefMap], SignalUseMap)

flattenExpr binds lam@(Lam b expr) = do
  -- Find the type of the binder
  let (arg_ty, _) = Type.splitFunTy (CoreUtils.exprType lam)
  -- Create signal names for the binder
  defs <- genSignalUses arg_ty
  let binds' = (b, Left defs):binds
  (args, res) <- flattenExpr binds' expr
  return ((useMapToDefMap defs) : args, res)

flattenExpr binds (Var id) =
  case bind of
    Left sig_use -> return ([], sig_use)
    Right _ -> error "Higher order functions not supported."
  where
    bind = Maybe.fromMaybe
      (error $ "Argument " ++ Name.getOccString id ++ "is unknown")
      (lookup id binds)

flattenExpr _ _ = do
  return ([], Tuple [])


-- vim: set ts=8 sw=2 sts=2 expandtab:
