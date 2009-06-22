--
-- Some types used by the VHDL module.
--
{-# LANGUAGE TemplateHaskell #-}
module VHDLTypes where

-- Standard imports
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import Data.Accessor
import qualified Data.Accessor.Template

-- GHC API imports
import qualified Type
import qualified CoreSyn

-- ForSyDe imports
import qualified ForSyDe.Backend.VHDL.AST as AST

-- Local imports
import FlattenTypes
import HsValueMap

type VHDLSignalMapElement = (Maybe (AST.VHDLId, AST.TypeMark))
-- | A mapping from a haskell structure to the corresponding VHDL port
--   signature, or Nothing for values that do not translate to a port.
type VHDLSignalMap = HsValueMap VHDLSignalMapElement

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity { 
  ent_id     :: AST.VHDLId,           -- The id of the entity
  ent_args   :: [VHDLSignalMapElement],      -- A mapping of each function argument to port names
  ent_res    :: VHDLSignalMapElement         -- A mapping of the function result to port names
} deriving (Show);

-- A orderable equivalent of CoreSyn's Type for use as a map key
newtype OrdType = OrdType { getType :: Type.Type }
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.tcEqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.tcCmpType a b

-- A map of a Core type to the corresponding type name
type TypeMap = Map.Map OrdType (AST.VHDLId, Either AST.TypeDef AST.SubtypeIn)

-- A map of Elem types to the corresponding VHDL Id for the Vector
type ElemTypeMap = Map.Map OrdType (AST.VHDLId, AST.TypeDef)

-- A map of a vector Core type to the coressponding VHDL functions
type TypeFunMap = Map.Map OrdType [AST.SubProgBody]

-- A map of a Haskell function to a hardware signature
type SignatureMap = Map.Map CoreSyn.CoreBndr Entity

-- A map of a builtin function to VHDL function builder 
type NameTable = Map.Map String (Int, [AST.Expr] -> AST.Expr )

data VHDLSession = VHDLSession {
  -- | A map of Core type -> VHDL Type
  vsTypes_      :: TypeMap,
  -- | A map of Elem types -> VHDL Vector Id
  vsElemTypes_   :: ElemTypeMap,
  -- | A map of vector Core type -> VHDL type function
  vsTypeFuns_   :: TypeFunMap,
  -- | A map of HsFunction -> hardware signature (entity name, port names,
  --   etc.)
  vsSignatures_ :: SignatureMap,
  -- | A map of Vector HsFunctions -> VHDL function call
  vsNameTable_  :: NameTable
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''VHDLSession )

-- | The state containing a VHDL Session
type VHDLState = State.State VHDLSession

-- | A substate containing just the types
type TypeState = State.State TypeMap

-- vim: set ts=8 sw=2 sts=2 expandtab:
