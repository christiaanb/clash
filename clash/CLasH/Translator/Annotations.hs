{-# LANGUAGE DeriveDataTypeable #-}
module CLasH.Translator.Annotations where
  
import qualified Language.Haskell.TH as TH
import Data.Data

data CLasHAnn = TopEntity | InitState TH.Name | TestInput | TestCycles
  deriving (Show, Data, Typeable)
  
isTopEntity :: CLasHAnn -> Bool
isTopEntity TopEntity = True
isTopEntity _         = False

isInitState :: CLasHAnn -> Bool
isInitState (InitState _) = True
isInitState _             = False

isTestInput :: CLasHAnn -> Bool
isTestInput TestInput = True
isTestInput _         = False

isTestCycles :: CLasHAnn -> Bool
isTestCycles TestCycles = True
isTestCycles _          = False