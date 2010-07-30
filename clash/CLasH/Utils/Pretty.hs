module CLasH.Utils.Pretty (prettyShow, pprString, pprStringDebug, zEncodeString) where

-- Standard imports
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJClass
import Data.Char
import Numeric

-- GHC API
import qualified CoreSyn
import Outputable ( showSDoc, showSDocDebug, ppr, Outputable, OutputableBndr)

-- VHDL Imports 
import qualified Language.VHDL.Ppr as Ppr
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.AST.Ppr

-- Local imports
import CLasH.VHDL.VHDLTypes
import CLasH.Utils.Core.CoreShow

-- | A version of the default pPrintList method, which uses a custom function
--   f instead of pPrint to print elements.
printList :: (a -> Doc) -> [a] -> Doc
printList f = brackets . fsep . punctuate comma . map f

{-
instance Pretty FuncData where
  pPrint (FuncData flatfunc entity arch) =
    text "Flattened: " $$ nest 15 (ppffunc flatfunc)
    $+$ text "Entity" $$ nest 15 (ppent entity)
    $+$ pparch arch
    where
      ppffunc (Just f) = pPrint f
      ppffunc Nothing  = text "Nothing"
      ppent (Just e)   = pPrint e
      ppent Nothing    = text "Nothing"
      pparch Nothing = text "VHDL architecture not present"
      pparch (Just _) = text "VHDL architecture present"
-}

instance Pretty Entity where
  pPrint (Entity id args res decl) =
    text "Entity: " $$ nest 10 (pPrint id)
    $+$ text "Args: " $$ nest 10 (pPrint args)
    $+$ text "Result: " $$ nest 10 (pPrint res)
    $+$ text "Declaration not shown"

instance (OutputableBndr b, Show b) => Pretty (CoreSyn.Bind b) where
  pPrint (CoreSyn.NonRec b expr) =
    text "NonRec: " $$ nest 10 (prettyBind (b, expr))
  pPrint (CoreSyn.Rec binds) =
    text "Rec: " $$ nest 10 (vcat $ map (prettyBind) binds)

instance (OutputableBndr b, Show b) => Pretty (CoreSyn.Expr b) where
  pPrint = text . show

instance Pretty AST.VHDLId where
  pPrint id = Ppr.ppr id
  
instance Pretty AST.VHDLName where
  pPrint name = Ppr.ppr name

prettyBind :: (Show b, Show e) => (b, e) -> Doc
prettyBind (b, expr) =
  text b' <> text " = " <> text expr'
  where
    b' = show b
    expr' = show expr

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pPrint = 
    vcat . map ppentry . Map.toList
    where
      ppentry (k, v) =
        pPrint k <> text " : " $$ nest 15 (pPrint v)

-- Convenience method for turning an Outputable into a string
pprString :: (Outputable x) => x -> String
pprString = showSDoc . ppr

pprStringDebug :: (Outputable x) => x -> String
pprStringDebug = showSDocDebug . ppr


type UserString = String        -- As the user typed it
type EncodedString = String     -- Encoded form

zEncodeString :: UserString -> EncodedString
zEncodeString cs = case maybe_tuple cs of
                Just n  -> n ++ (go cs)            -- Tuples go to Z2T etc
                Nothing -> go cs
          where
                go []     = []
                go (c:cs) = encode_digit_ch c ++ go' cs
                go' []     = []
                go' (c:cs) = encode_ch c ++ go' cs

maybe_tuple :: UserString -> Maybe EncodedString

maybe_tuple "(# #)" = Just("Z1H")
maybe_tuple ('(' : '#' : cs) = case count_commas (0::Int) cs of
                                 (n, '#' : ')' : _) -> Just ('Z' : shows (n+1) "H")
                                 _                  -> Nothing
maybe_tuple "()" = Just("Z0T")
maybe_tuple ('(' : cs)       = case count_commas (0::Int) cs of
                                 (n, ')' : _) -> Just ('Z' : shows (n+1) "T")
                                 _            -> Nothing
maybe_tuple _                = Nothing

count_commas :: Int -> String -> (Int, String)
count_commas n (',' : cs) = count_commas (n+1) cs
count_commas n cs         = (n,cs)

encode_digit_ch :: Char -> EncodedString
encode_digit_ch c | c >= '0' && c <= '9' = encode_as_unicode_char c
encode_digit_ch c | otherwise            = encode_ch c

encode_ch :: Char -> EncodedString
encode_ch c | unencodedChar c = [c]     -- Common case first

-- Constructors
encode_ch '('  = "ZL"   -- Needed for things like (,), and (->)
encode_ch ')'  = "ZR"   -- For symmetry with (
encode_ch '['  = "ZM"
encode_ch ']'  = "ZN"
encode_ch ':'  = "ZC"

-- Variables
encode_ch '&'  = "za"
encode_ch '|'  = "zb"
encode_ch '^'  = "zc"
encode_ch '$'  = "zd"
encode_ch '='  = "ze"
encode_ch '>'  = "zg"
encode_ch '#'  = "zh"
encode_ch '.'  = "zi"
encode_ch '<'  = "zl"
encode_ch '-'  = "zm"
encode_ch '!'  = "zn"
encode_ch '+'  = "zp"
encode_ch '\'' = "zq"
encode_ch '\\' = "zr"
encode_ch '/'  = "zs"
encode_ch '*'  = "zt"
encode_ch '%'  = "zv"
encode_ch c    = encode_as_unicode_char c

encode_as_unicode_char :: Char -> EncodedString
encode_as_unicode_char c = 'z' : if isDigit (head hex_str) then hex_str
                                                           else '0':hex_str
  where hex_str = showHex (ord c) "U"
                                                           
unencodedChar :: Char -> Bool   -- True for chars that don't need encoding
unencodedChar c   =  c >= 'a' && c <= 'z'
                  || c >= 'A' && c <= 'Z'
                  || c >= '0' && c <= '9'
                  || c == '_'                                                         