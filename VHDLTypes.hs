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

-- ForSyDe imports
import qualified ForSyDe.Backend.VHDL.AST as AST

-- Local imports
import FlattenTypes
import HsValueMap

-- | A mapping from a haskell structure to the corresponding VHDL port
--   signature, or Nothing for values that do not translate to a port.
type VHDLSignalMap = HsValueMap (Maybe (AST.VHDLId, AST.TypeMark))

-- A description of a VHDL entity. Contains both the entity itself as well as
-- info on how to map a haskell value (argument / result) on to the entity's
-- ports.
data Entity = Entity {
  ent_id     :: AST.VHDLId,           -- The id of the entity
  ent_args   :: [VHDLSignalMap],      -- A mapping of each function argument to port names
  ent_res    :: VHDLSignalMap         -- A mapping of the function result to port names
} deriving (Show);

-- A orderable equivalent of CoreSyn's Type for use as a map key
newtype OrdType = OrdType Type.Type
instance Eq OrdType where
  (OrdType a) == (OrdType b) = Type.tcEqType a b
instance Ord OrdType where
  compare (OrdType a) (OrdType b) = Type.tcCmpType a b

-- A map of a Core type to the corresponding type name (and optionally, it's
-- declaration for non-primitive types).
type TypeMap = Map.Map OrdType (AST.VHDLId, AST.TypeDec)

-- A map of a Haskell function to a hardware signature
type SignatureMap = Map.Map HsFunction Entity

data VHDLSession = VHDLSession {
  -- | A map of Core type -> VHDL Type
  vsTypes_ :: TypeMap,
  -- | A map of HsFunction -> hardware signature (entity name, port names,
  --   etc.)
  vsSignatures_ :: SignatureMap
}

-- Derive accessors
$( Data.Accessor.Template.deriveAccessors ''VHDLSession )

type VHDLState = State.State VHDLSession

-- vim: set ts=8 sw=2 sts=2 expandtab:
