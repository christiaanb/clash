module Pretty (prettyShow) where

import qualified Data.Map as Map
import qualified CoreSyn
import qualified Module
import qualified HscTypes
import Text.PrettyPrint.HughesPJClass
import Outputable ( showSDoc, ppr, Outputable, OutputableBndr)

import qualified ForSyDe.Backend.Ppr
import qualified ForSyDe.Backend.VHDL.AST as AST

import HsValueMap
import FlattenTypes
import TranslatorTypes
import VHDLTypes

-- | A version of the default pPrintList method, which uses a custom function
--   f instead of pPrint to print elements.
printList :: (a -> Doc) -> [a] -> Doc
printList f = brackets . fsep . punctuate comma . map f

instance Pretty HsFunction where
  pPrint (HsFunction name args res) =
    text name <> char ' ' <> parens (hsep $ punctuate comma args') <> text " -> " <> res'
    where
      args' = map pPrint args
      res'  = pPrint res

instance Pretty x => Pretty (HsValueMap x) where
  pPrint (Tuple maps) = parens (hsep $ punctuate comma (map pPrint maps))
  pPrint (Single s)   = pPrint s

instance Pretty HsValueUse where
  pPrint Port            = char 'P'
  pPrint (State n)       = char 'C' <> int n
  pPrint (HighOrder _ _) = text "Higher Order"

instance Pretty FlatFunction where
  pPrint (FlatFunction args res defs sigs) =
    (text "Args: ") $$ nest 10 (pPrint args)
    $+$ (text "Result: ") $$ nest 10 (pPrint res)
    $+$ (text "Defs: ") $$ nest 10 (pPrint defs)
    $+$ text "Signals: " $$ nest 10 (printList ppsig sigs)
    where
      ppsig (id, info) = pPrint id <> pPrint info

instance Pretty SigDef where
  pPrint (FApp func args res) =
    pPrint func <> text " : " <> pPrint args <> text " -> " <> pPrint res
  pPrint (CondDef _ _ _ _) = text "TODO"
  pPrint (UncondDef src dst) = text "TODO"

instance Pretty SignalInfo where
  pPrint (SignalInfo name use ty) =
    text ":" <> (pPrint use) <> (ppname name)
    where
      ppname Nothing = empty
      ppname (Just name) = text ":" <> text name

instance Pretty SigUse where
  pPrint SigPortIn   = text "PI"
  pPrint SigPortOut  = text "PO"
  pPrint SigInternal = text "I"
  pPrint (SigStateOld n) = text "SO:" <> int n
  pPrint (SigStateNew n) = text "SN:" <> int n
  pPrint SigSubState = text "s"

instance Pretty VHDLSession where
  pPrint (VHDLSession mod nameCount funcs) =
    text "Module: " $$ nest 15 (text modname)
    $+$ text "NameCount: " $$ nest 15 (int nameCount)
    $+$ text "Functions: " $$ nest 15 (vcat (map ppfunc (Map.toList funcs)))
    where
      ppfunc (hsfunc, fdata) =
        pPrint hsfunc $+$ nest 5 (pPrint fdata)
      modname = showSDoc $ Module.pprModule (HscTypes.cm_module mod)

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

instance Pretty Entity where
  pPrint (Entity id args res decl) =
    text "Entity: " $$ nest 10 (pPrint id)
    $+$ text "Args: " $$ nest 10 (pPrint args)
    $+$ text "Result: " $$ nest 10 (pPrint res)
    $+$ ppdecl decl
    where
      ppdecl Nothing = text "VHDL entity not present"
      ppdecl (Just _) = text "VHDL entity present"

instance (OutputableBndr b) => Pretty (CoreSyn.Bind b) where
  pPrint (CoreSyn.NonRec b expr) =
    text "NonRec: " $$ nest 10 (prettyBind (b, expr))
  pPrint (CoreSyn.Rec binds) =
    text "Rec: " $$ nest 10 (vcat $ map (prettyBind) binds)

instance Pretty AST.VHDLId where
  pPrint id = ForSyDe.Backend.Ppr.ppr id

prettyBind :: (Outputable b, Outputable e) => (b, e) -> Doc
prettyBind (b, expr) =
  text b' <> text " = " <> text expr'
  where
    b' = showSDoc $ ppr b
    expr' = showSDoc $ ppr expr
