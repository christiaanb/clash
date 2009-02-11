--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

import Flatten
import qualified Type
import qualified Name
import qualified TyCon
import qualified Maybe
import Outputable ( showSDoc, ppr )
import qualified ForSyDe.Backend.VHDL.AST as AST

-- | The VHDL Bit type
bit_ty :: AST.TypeMark
bit_ty = AST.unsafeVHDLBasicId "Bit"

-- Translate a Haskell type to a VHDL type
vhdl_ty :: Type.Type -> AST.TypeMark
vhdl_ty ty = Maybe.fromMaybe
  (error $ "Unsupported Haskell type: " ++ (showSDoc $ ppr ty))
  (vhdl_ty_maybe ty)

-- Translate a Haskell type to a VHDL type
vhdl_ty_maybe :: Type.Type -> Maybe AST.TypeMark
vhdl_ty_maybe ty =
  case Type.splitTyConApp_maybe ty of
    Just (tycon, args) ->
      let name = TyCon.tyConName tycon in
        -- TODO: Do something more robust than string matching
        case Name.getOccString name of
          "Bit"      -> Just bit_ty
          otherwise  -> Nothing
    otherwise -> Nothing

-- Shortcut
mkVHDLId :: String -> AST.VHDLId
mkVHDLId = AST.unsafeVHDLBasicId

