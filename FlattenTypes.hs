module FlattenTypes where

import qualified Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Control.Monad.Trans.State as State

import CoreSyn
import qualified Type

import HsValueMap
import CoreShow

-- | A signal identifier
type SignalId = Int

-- | A map of a Haskell value to signal ids
type SignalMap = HsValueMap SignalId

-- | A state identifier
type StateId = Int

-- | How is a given (single) value in a function's type (ie, argument or
--   return value) used?
data HsValueUse = 
  Port           -- ^ Use it as a port (input or output)
  | State StateId -- ^ Use it as state (input or output). The int is used to
                 --   match input state to output state.
  | HighOrder {  -- ^ Use it as a high order function input
    hoName :: String,  -- ^ Which function is passed in?
    hoArgs :: [HsUseMap]   -- ^ Which arguments are already applied? This
                         -- ^ map should only contain Port and other
                         --   HighOrder values. 
  }
  deriving (Show, Eq, Ord)

-- | Is this HsValueUse a state use?
isStateUse :: HsValueUse -> Bool
isStateUse (State _) = True
isStateUse _         = False

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

hasState :: HsFunction -> Bool
hasState hsfunc = 
  any (Foldable.any isStateUse) (hsFuncArgs hsfunc)
  || Foldable.any isStateUse (hsFuncRes hsfunc)

-- | Something that defines a signal
data SigDef =
  -- | A flattened function application
  FApp {
    appFunc :: HsFunction,
    appArgs :: [SignalMap],
    appRes  :: SignalMap
  }
  -- | A conditional signal definition
  | CondDef {
    cond    :: SignalId,
    high    :: SignalId,
    low     :: SignalId,
    condRes :: SignalId
  }
  -- | Unconditional signal definition
  | UncondDef {
    defSrc :: Either SignalId SignalExpr,
    defDst :: SignalId
  } deriving (Show, Eq)

-- | Is the given SigDef a FApp?
is_FApp :: SigDef -> Bool
is_FApp d = case d of  
  (FApp _ _ _) -> True
  _ -> False

-- | Which signals are used by the given SigDef?
sigDefUses :: SigDef -> [SignalId]
sigDefUses (UncondDef (Left id) _) = [id]
sigDefUses (UncondDef (Right expr) _) = sigExprUses expr
sigDefUses (CondDef cond true false _) = [cond, true, false]
sigDefUses (FApp _ args _) = concat $ map Foldable.toList args

-- | An expression on signals
data SignalExpr = 
  EqLit SignalId String -- ^ Is the given signal equal to the given (VHDL) literal
  | Literal String (Maybe Type.Type)-- ^ A literal value, with an optional type to cast to
  | Eq SignalId SignalId -- ^ A comparison between to signals
  deriving (Show, Eq)

-- Instantiate Eq for Type, so we can derive Eq for SignalExpr.
instance Eq Type.Type where
  (==) = Type.coreEqType

-- | Which signals are used by the given SignalExpr?
sigExprUses :: SignalExpr -> [SignalId]
sigExprUses (EqLit id _) = [id]
sigExprUses (Literal _ _) = []
sigExprUses (Eq a b) = [a, b]

-- Returns the function used by the given SigDef, if any
usedHsFunc :: SigDef -> Maybe HsFunction
usedHsFunc (FApp hsfunc _ _) = Just hsfunc
usedHsFunc _ = Nothing

-- | How is a given signal used in the resulting VHDL?
data SigUse = 
  SigPortIn          -- | Use as an input port
  | SigPortOut       -- | Use as an input port
  | SigInternal      -- | Use as an internal signal
  | SigStateOld StateId  -- | Use as the current internal state
  | SigStateNew StateId  -- | Use as the new internal state
  | SigSubState      -- | Do not use, state variable is used in a subcircuit
  deriving (Show)

-- | Is this a port signal use?
isPortSigUse :: SigUse -> Bool
isPortSigUse SigPortIn = True
isPortSigUse SigPortOut = True
isPortSigUse _ = False

-- | Is this a state signal use? Returns false for substate.
isStateSigUse :: SigUse -> Bool
isStateSigUse (SigStateOld _) = True
isStateSigUse (SigStateNew _) = True
isStateSigUse _ = False

-- | Is this an internal signal use?
isInternalSigUse :: SigUse -> Bool
isInternalSigUse SigInternal = True
isInternalSigUse _ = False

oldStateId :: SigUse -> Maybe StateId
oldStateId (SigStateOld id) = Just id
oldStateId _ = Nothing

newStateId :: SigUse -> Maybe StateId
newStateId (SigStateNew id) = Just id
newStateId _ = Nothing

-- | Information on a signal definition
data SignalInfo = SignalInfo {
  sigName :: Maybe String,
  sigUse  :: SigUse,
  sigTy   :: Type.Type,
  nameHints :: [String]
} deriving (Show)

-- | A flattened function
data FlatFunction = FlatFunction {
  flat_args   :: [SignalMap],
  flat_res    :: SignalMap,
  flat_defs   :: [SigDef],
  flat_sigs   :: [(SignalId, SignalInfo)]
} deriving (Show)

-- | Lookup a given signal id in a signal map, and return the associated
--   SignalInfo. Errors out if the signal was not found.
signalInfo :: [(SignalId, SignalInfo)] -> SignalId -> SignalInfo
signalInfo sigs id = Maybe.fromJust $ lookup id sigs

-- | A list of binds in effect at a particular point of evaluation
type BindMap = [(
  CoreBndr,            -- ^ The bind name
  BindValue            -- ^ The value bound to it
  )]

type BindValue =
  Either               -- ^ The bind value which is either
    (SignalMap)
                       -- ^ a signal
    (
      HsValueUse,      -- ^ or a HighOrder function
      [SignalId]       -- ^ With these signals already applied to it
    )

-- | The state during the flattening of a single function
type FlattenState = State.State ([SigDef], [(SignalId, SignalInfo)], SignalId)

-- | Add an application to the current FlattenState
addDef :: SigDef -> FlattenState ()
addDef d = do
  (defs, sigs, n) <- State.get
  State.put (d:defs, sigs, n)

-- | Generates a new signal id, which is unique within the current flattening.
genSignalId :: SigUse -> Type.Type -> FlattenState SignalId 
genSignalId use ty = do
  (defs, sigs, n) <- State.get
  -- Generate a new numbered but unnamed signal
  let s = (n, SignalInfo Nothing use ty [])
  State.put (defs, s:sigs, n+1)
  return n

-- | Add a name hint to the given signal
addNameHint :: String -> SignalId -> FlattenState ()
addNameHint hint id = do
  info <- getSignalInfo id
  let hints = nameHints info
  if hint `elem` hints
    then do
      return ()
    else do
      let hints' = (hint:hints)
      setSignalInfo id (info {nameHints = hints'})

-- | Returns the SignalInfo for the given signal. Errors if the signal is not
--   known in the session.
getSignalInfo :: SignalId -> FlattenState SignalInfo
getSignalInfo id = do
  (defs, sigs, n) <- State.get
  return $ signalInfo sigs id

setSignalInfo :: SignalId -> SignalInfo -> FlattenState ()
setSignalInfo id' info' = do
  (defs, sigs, n) <- State.get
  let sigs' = map (\(id, info) -> (id, if id == id' then info' else info)) sigs
  State.put (defs, sigs', n)

-- vim: set ts=8 sw=2 sts=2 expandtab:
