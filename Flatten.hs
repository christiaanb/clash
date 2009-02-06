module Flatten where
import Translator (HsValueMap)


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
-- vim: set ts=8 sw=2 sts=2 expandtab:
