--
-- Simple module providing some types used by Translator. These are in a
-- separate module to prevent circular dependencies in Pretty for example.
--
{-# LANGUAGE TemplateHaskell #-}
module CLasH.Translator.TranslatorTypes where

-- Standard modules
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import qualified Data.Accessor.Template
import Data.Accessor

-- GHC API
import qualified CoreSyn
import qualified Type
import qualified HscTypes
import qualified UniqSupply

-- ForSyDe
import qualified Language.VHDL.AST as AST

-- Local imports
import CLasH.VHDL.VHDLTypes

-- A orderable equivalent of CoreSyn's Type for use as a map key
newtype OrdType = OrdType { getType :: Type.Type }
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.tcEqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.tcCmpType a b

data HType = StdType OrdType |
             ADTType String [HType] |
             VecType Int HType |
             SizedWType Int |
             RangedWType Int |
             SizedIType Int |
             BuiltinType String
  deriving (Eq, Ord)

-- A map of a Core type to the corresponding type name
type TypeMap = Map.Map HType (AST.VHDLId, Either AST.TypeDef AST.SubtypeIn)

-- A map of a vector Core element type and function name to the coressponding
-- VHDLId of the function and the function body.
type TypeFunMap = Map.Map (OrdType, String) (AST.VHDLId, AST.SubProgBody)

type TfpIntMap = Map.Map OrdType Int
-- A substate that deals with type generation
data TypeState = TypeState {
  -- | A map of Core type -> VHDL Type
  tsTypes_      :: TypeMap,
  -- | A list of type declarations
  tsTypeDecls_  :: [AST.PackageDecItem],
  -- | A map of vector Core type -> VHDL type function
  tsTypeFuns_   :: TypeFunMap,
  tsTfpInts_    :: TfpIntMap,
  tsHscEnv_     :: HscTypes.HscEnv
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''TypeState )

-- Define a session
type TypeSession = State.State TypeState
-- A global state for the translator
data TranslatorState = TranslatorState {
    tsUniqSupply_ :: UniqSupply.UniqSupply
  , tsType_ :: TypeState
  , tsBindings_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , tsNormalized_ :: Map.Map CoreSyn.CoreBndr CoreSyn.CoreExpr
  , tsEntities_ :: Map.Map CoreSyn.CoreBndr Entity
  , tsArchitectures_ :: Map.Map CoreSyn.CoreBndr (Architecture, [CoreSyn.CoreBndr])
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''TranslatorState )

type TranslatorSession = State.State TranslatorState

-- Does the given binder reference a top level binder in the current
-- module(s)?
isTopLevelBinder :: CoreSyn.CoreBndr -> TranslatorSession Bool
isTopLevelBinder bndr = do
  bindings <- getA tsBindings
  return $ Map.member bndr bindings

-- vim: set ts=8 sw=2 sts=2 expandtab:
