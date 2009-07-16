{-# LANGUAGE DeriveDataTypeable #-}
module CLasH.Translator.Annotations where
  
import Language.Haskell.TH
import Data.Data

data CLasHAnn = TopEntity | InitState
  deriving (Show, Data, Typeable)
  
isTopEntity :: CLasHAnn -> Bool
isTopEntity TopEntity = True
isTopEntity _         = False

isInitState :: CLasHAnn -> Bool
isInitState InitState = True
isInitState _         = False