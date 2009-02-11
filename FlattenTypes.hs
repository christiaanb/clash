module FlattenTypes where

import Data.Traversable
import qualified Control.Monad.State as State

import CoreSyn

import HsValueMap

-- | A signal identifier
type UnnamedSignal = Int

-- | A map of a Haskell value to signal ids
type SignalMap sigid = HsValueMap sigid

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
  deriving (Show, Eq, Ord)

-- | A map from a Haskell value to the use of each single value
type HsUseMap = HsValueMap HsValueUse

-- | Builds a HsUseMap with the same structure has the given HsValueMap in
--   which all the Single elements are marked as State, with increasing state
--   numbers.
useAsState :: HsValueMap a -> HsUseMap
useAsState map =
  map'
  where
    -- Traverse the existing map, resulting in a function that maps an initial
    -- state number to the final state number and the new map
    PassState f = traverse asState map
    -- Run this function to get the new map
    (_, map')   = f 0
    -- This function maps each element to a State with a unique number, by
    -- incrementing the state count.
    asState x   = PassState (\s -> (s+1, State s))

-- | Builds a HsUseMap with the same structure has the given HsValueMap in
--   which all the Single elements are marked as Port.
useAsPort :: HsValueMap a -> HsUseMap
useAsPort map = fmap (\x -> Port) map

-- | A Haskell function with a specific signature. The signature defines what
--   use the arguments and return value of the function get.
data HsFunction = HsFunction {
  hsFuncName :: String,
  hsFuncArgs :: [HsUseMap],
  hsFuncRes  :: HsUseMap
} deriving (Show, Eq, Ord)

-- | A flattened function application
data FApp sigid = FApp {
  appFunc :: HsFunction,
  appArgs :: [SignalMap sigid],
  appRes  :: SignalMap sigid
} deriving (Show, Eq)

-- | A conditional signal definition
data CondDef sigid = CondDef {
  cond    :: sigid,
  high    :: sigid,
  low     :: sigid,
  condRes :: sigid
} deriving (Show, Eq)

-- | Information on a signal definition
data Signal sigid = Signal {
  id :: sigid
} deriving (Eq, Show)

-- | A flattened function
data FlatFunction' sigid = FlatFunction {
  args   :: [SignalMap sigid],
  res    :: SignalMap sigid,
  apps   :: [FApp sigid],
  conds  :: [CondDef sigid],
  sigs   :: [Signal sigid]
} deriving (Show, Eq)

-- | A flat function that does not have its signals named
type FlatFunction = FlatFunction' UnnamedSignal

-- | A list of binds in effect at a particular point of evaluation
type BindMap = [(
  CoreBndr,            -- ^ The bind name
  Either               -- ^ The bind value which is either
    (SignalMap UnnamedSignal)
                       -- ^ a signal
    (
      HsValueUse,      -- ^ or a HighOrder function
      [UnnamedSignal]  -- ^ With these signals already applied to it
    )
  )]

-- | The state during the flattening of a single function
type FlattenState = State.State ([FApp UnnamedSignal], [CondDef UnnamedSignal], [Signal UnnamedSignal], UnnamedSignal)

-- | Add an application to the current FlattenState
addApp :: (FApp UnnamedSignal) -> FlattenState ()
addApp a = do
  (apps, conds, sigs, n) <- State.get
  State.put (a:apps, conds, sigs, n)

-- | Add a conditional definition to the current FlattenState
addCondDef :: (CondDef UnnamedSignal) -> FlattenState ()
addCondDef c = do
  (apps, conds, sigs, n) <- State.get
  State.put (apps, c:conds, sigs, n)

-- | Generates a new signal id, which is unique within the current flattening.
genSignalId :: FlattenState UnnamedSignal 
genSignalId = do
  (apps, conds, sigs, n) <- State.get
  let s = Signal n
  State.put (apps, conds, s:sigs, n+1)
  return n
