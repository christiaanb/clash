module CLasH.Utils.Pretty (prettyShow, pprString, pprStringDebug) where


import qualified Data.Map as Map
import qualified Data.Foldable as Foldable
import qualified List

import qualified CoreSyn
import qualified Module
import qualified HscTypes
import Text.PrettyPrint.HughesPJClass
import Outputable ( showSDoc, showSDocDebug, ppr, Outputable, OutputableBndr)

import qualified Language.VHDL.Ppr as Ppr
import qualified Language.VHDL.AST as AST
import qualified Language.VHDL.AST.Ppr

import CLasH.Translator.TranslatorTypes
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
