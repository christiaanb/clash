module Pretty (prettyShow) where

import qualified Data.Map as Map
import qualified CoreSyn
import qualified Module
import qualified HscTypes
import Text.PrettyPrint.HughesPJClass
import Outputable ( showSDoc, ppr, Outputable, OutputableBndr)

import HsValueMap
import FlattenTypes
import TranslatorTypes

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

instance Pretty id => Pretty (FlatFunction' id) where
  pPrint (FlatFunction args res apps conds sigs) =
    (text "Args: ") $$ nest 10 (pPrint args)
    $+$ (text "Result: ") $$ nest 10 (pPrint res)
    $+$ (text "Apps: ") $$ nest 10 (vcat (map pPrint apps))
    $+$ (text "Conds: ") $$ nest 10 (pPrint conds)
    $+$ text "Signals: " $$ nest 10 (pPrint sigs)

instance Pretty id => Pretty (FApp id) where
  pPrint (FApp func args res) =
    pPrint func <> text " : " <> pPrint args <> text " -> " <> pPrint res

instance Pretty id => Pretty (CondDef id) where
  pPrint _ = text "TODO"

instance Pretty id => Pretty (Signal id) where
  pPrint (Signal id) = pPrint id

instance Pretty NamedSignal where
  pPrint (NamedSignal name) = pPrint name

instance Pretty VHDLSession where
  pPrint (VHDLSession mod nameCount funcs) =
    text "Module: " $$ nest 15 (text modname)
    $+$ text "NameCount: " $$ nest 15 (int nameCount)
    $+$ text "Functions: " $$ nest 15 (vcat (map ppfunc (Map.toList funcs)))
    where
      ppfunc (hsfunc, (FuncData flatfunc)) =
        pPrint hsfunc $+$ (text "Flattened: " $$ nest 15 (ppffunc flatfunc))
      ppffunc (Just (Left f)) = pPrint f
      ppffunc (Just (Right f)) = pPrint f
      ppffunc Nothing = text "Nothing"
      modname = showSDoc $ Module.pprModule (HscTypes.cm_module mod)

instance (OutputableBndr b) => Pretty (CoreSyn.Bind b) where
  pPrint (CoreSyn.NonRec b expr) =
    text "NonRec: " $$ nest 10 (prettyBind (b, expr))
  pPrint (CoreSyn.Rec binds) =
    text "Rec: " $$ nest 10 (vcat $ map (prettyBind) binds)

prettyBind :: (Outputable b, Outputable e) => (b, e) -> Doc
prettyBind (b, expr) =
  text b' <> text " = " <> text expr'
  where
    b' = showSDoc $ ppr b
    expr' = showSDoc $ ppr expr
