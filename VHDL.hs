--
-- Functions to generate VHDL from FlatFunctions
--
module VHDL where

import Data.Traversable
import qualified Maybe

import qualified Type
import qualified Name
import qualified TyCon
import Outputable ( showSDoc, ppr )

import qualified ForSyDe.Backend.VHDL.AST as AST

import VHDLTypes
import FlattenTypes
import TranslatorTypes

-- | Create an entity for a given function
createEntity ::
  HsFunction        -- | The function signature
  -> FuncData       -- | The function data collected so far
  -> FuncData       -- | The modified function data

createEntity hsfunc fdata = 
  let func = flatFunc fdata in
  case func of
    -- Skip (builtin) functions without a FlatFunction
    Nothing -> fdata
    -- Create an entity for all other functions
    Just flatfunc ->
      
      let 
        s       = sigs flatfunc
        a       = args flatfunc
        r       = res  flatfunc
        args'   = map (fmap (mkMap s)) a
        res'    = fmap (mkMap s) r
        entity' = Entity args' res' Nothing
      in
        fdata { entity = Just entity' }
  where
    mkMap :: Eq id => [(id, SignalInfo)] -> id -> AST.VHDLId
    mkMap sigmap id =
      mkVHDLId nm
      where
        info = Maybe.fromMaybe
          (error $ "Signal not found in the name map? This should not happen!")
          (lookup id sigmap)
        nm = Maybe.fromMaybe
          (error $ "Signal not named? This should not happen!")
          (name info)
      




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
