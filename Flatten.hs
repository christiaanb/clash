module Flatten where
import CoreSyn
import qualified Control.Monad.State as State

-- | A datatype that maps each of the single values in a haskell structure to
-- a mapto. The map has the same structure as the haskell type mapped, ie
-- nested tuples etc.
data HsValueMap mapto =
  Tuple [HsValueMap mapto]
  | Single mapto
  | Unused
  deriving (Show, Eq)

data FlatFunction = FlatFunction {
  args   :: [SignalDefMap],
  res    :: SignalUseMap,
  --sigs   :: [SignalDef],
  apps   :: [App],
  conds  :: [CondDef]
} deriving (Show, Eq)
    
type SignalUseMap = HsValueMap SignalUse
type SignalDefMap = HsValueMap SignalDef

data SignalUse = SignalUse {
  sigUseId :: Int
} deriving (Show, Eq)

data SignalDef = SignalDef {
  sigDefId :: Int
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
  String,              -- ^ The bind name
  Either               -- ^ The bind value which is either
    SignalUse          -- ^ a signal
    (
      HsValueUse,      -- ^ or a HighOrder function
      [SignalUse]      -- ^ With these signals already applied to it
    )
  )]

type FlattenState = State.State ([App], [CondDef], Int)

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
    (fres, end_state) = State.runState (flattenExpr expr) init_state
    (args, res)       = fres
    (apps, conds, _)  = end_state

flattenExpr ::
  CoreExpr
  -> FlattenState ([SignalDefMap], SignalUseMap)

flattenExpr _ = do
  return ([], Tuple [])




-- vim: set ts=8 sw=2 sts=2 expandtab:
