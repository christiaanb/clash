{-# LANGUAGE TemplateHaskell #-}
--
-- Simple module providing some types used by Translator. These are in a
-- separate module to prevent circular dependencies in Pretty for example.
--
module CLasH.Translator.TranslatorTypes where

-- Standard modules
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import qualified Data.Accessor.Template
import qualified Data.Accessor.Monad.Trans.State as MonadState

-- GHC API
import qualified GHC
import qualified CoreSyn
import qualified Type
import qualified HscTypes
import qualified UniqSupply

-- VHDL Imports
import qualified Language.VHDL.AST as AST

-- Local imports
import CLasH.VHDL.VHDLTypes

-- | A specification of an entity we can generate VHDL for. Consists of the
--   binder of the top level entity, an optional initial state and an optional
--   test input.
type EntitySpec = (Maybe CoreSyn.CoreBndr, Maybe [(CoreSyn.CoreBndr, CoreSyn.CoreBndr)], Maybe CoreSyn.CoreExpr)

-- | A function that knows which parts of a module to compile
type Finder =
  HscTypes.CoreModule -- ^ The module to look at
  -> GHC.Ghc [EntitySpec]

-----------------------------------------------------------------------------
-- The TranslatorSession
-----------------------------------------------------------------------------

-- A orderable equivalent of CoreSyn's Type for use as a map key
newtype OrdType = OrdType Type.Type
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.tcEqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.tcCmpType a b

data HType = AggrType String (Maybe (String, HType)) [[(String, HType)]] |
             -- ^ A type containing multiple fields. Arguments: Type
             -- name, an optional EnumType for the constructors (if > 1)
             -- and a list containing a list of fields (name, htype) for
             -- each constructor.
             EnumType String [String] |
             -- ^ A type containing no fields and multiple constructors.
             -- Arguments: Type name, a list of possible values.
             VecType Int HType |
             UVecType HType |
             SizedWType Int |
             RangedWType Int |
             SizedIType Int |
             BuiltinType String |
             UnitType |
             StateType
  deriving (Eq, Ord, Show)

-- A map of a Core type to the corresponding type name, or Nothing when the
-- type would be empty.
type TypeMapRec   = Maybe (AST.VHDLId, Maybe (Either AST.TypeDef AST.SubtypeIn))
type TypeMap      = Map.Map HType TypeMapRec

-- A map of a vector Core element type and function name to the coressponding
-- VHDLId of the function and the function body.
type TypeFunMap = Map.Map (HType, String) (AST.VHDLId, AST.SubProgBody)

type TfpIntMap = Map.Map OrdType Int
-- A substate that deals with type generation
data TypeState = TypeState {
  -- | A map of Core type -> VHDL Type
  tsTypes_      :: TypeMap,
  -- | A list of type declarations
  tsTypeDecls_  :: [Maybe AST.PackageDecItem],
  -- | A map of vector Core type -> VHDL type function
  tsTypeFuns_   :: TypeFunMap,
  tsTfpInts_    :: TfpIntMap,
  tsHscEnv_     :: HscTypes.HscEnv
}

-- Derive accessors
Data.Accessor.Template.deriveAccessors ''TypeState

-- Define a session
type TypeSession = State.State TypeState
-- A global state for the translator
data TranslatorState = TranslatorState {
    tsUniqSupply_ :: UniqSupply.UniqSupply
  , tsType_ :: TypeState
  , tsBindings_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , tsNormalized_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , tsEntityCounter_ :: Integer
  , tsEntities_ :: Map.Map CoreSyn.CoreBndr Entity
  , tsArchitectures_ :: Map.Map CoreSyn.CoreBndr (Architecture, [CoreSyn.CoreBndr])
  , tsInitStates_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreBndr
  , tsTransformCounter_ :: Int -- ^ How many transformations were applied?
  , tsArrows_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreBndr
}

-- Derive accessors
Data.Accessor.Template.deriveAccessors ''TranslatorState

type TranslatorSession = State.State TranslatorState

-----------------------------------------------------------------------------
-- Some accessors
-----------------------------------------------------------------------------

-- Does the given binder reference a top level binder in the current
-- module(s)?
isTopLevelBinder :: CoreSyn.CoreBndr -> TranslatorSession Bool
isTopLevelBinder bndr = do
  bindings <- MonadState.get tsBindings
  return $ Map.member bndr bindings

-- Finds the value of a global binding, if available
getGlobalBind :: CoreSyn.CoreBndr -> TranslatorSession (Maybe CoreSyn.CoreExpr)
getGlobalBind bndr = do
  bindings <- MonadState.get tsBindings
  return $ Map.lookup bndr bindings 

-- Adds a new global binding with the given value
addGlobalBind :: CoreSyn.CoreBndr -> CoreSyn.CoreExpr -> TranslatorSession ()
addGlobalBind bndr expr = MonadState.modify tsBindings (Map.insert bndr expr)

-- Returns a list of all global binders
getGlobalBinders :: TranslatorSession [CoreSyn.CoreBndr]
getGlobalBinders = do
  bindings <- MonadState.get tsBindings
  return $ Map.keys bindings

-- vim: set ts=8 sw=2 sts=2 expandtab:
