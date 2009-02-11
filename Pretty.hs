module Pretty (prettyShow) where

import qualified CoreSyn
import Text.PrettyPrint.HughesPJClass
import Outputable ( showSDoc, ppr, Outputable, OutputableBndr)
import Flatten
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

instance Pretty FlatFunction where
  pPrint (FlatFunction args res apps conds) =
    (text "Args: ") $$ nest 10 (pPrint args)
    $+$ (text "Result: ") $$ nest 10 (pPrint res)
    $+$ (text "Apps: ") $$ nest 10 (vcat (map pPrint apps))
    $+$ (text "Conds: ") $$ nest 10 (pPrint conds)

instance Pretty FApp where
  pPrint (FApp func args res) =
    pPrint func <> text " : " <> pPrint args <> text " -> " <> pPrint res

instance Pretty SignalDef where
  pPrint (SignalDef id) = pPrint id

instance Pretty SignalUse where
  pPrint (SignalUse id) = pPrint id

instance Pretty CondDef where
  pPrint _ = text "TODO"

instance Pretty VHDLSession where
  pPrint (VHDLSession nameCount funcs) =
    text "NameCount: " $$ nest 15 (int nameCount)
    $+$ text "Functions: " $$ nest 15 (vcat (map ppfunc funcs))
    where
      ppfunc (hsfunc, (flatfunc)) =
        pPrint hsfunc $+$ (text "Flattened: " $$ nest 15 (pPrint flatfunc))

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
