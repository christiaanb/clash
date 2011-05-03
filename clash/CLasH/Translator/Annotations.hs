{-# LANGUAGE DeriveDataTypeable #-}
module CLasH.Translator.Annotations where
  
import qualified Language.Haskell.TH as TH
import Data.Data

data CLasHAnn = TopEntity | TestInput
  deriving (Show, Data, Typeable)
  
isTopEntity :: CLasHAnn -> Bool
isTopEntity TopEntity = True
isTopEntity _         = False

isTestInput :: CLasHAnn -> Bool
isTestInput TestInput = True
isTestInput _         = False
