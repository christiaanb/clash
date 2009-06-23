{-# LANGUAGE TemplateHaskell #-}

module GlobalNameTable (globalNameTable) where

import Language.Haskell.TH
import qualified Data.Map as Map

import qualified ForSyDe.Backend.VHDL.AST as AST
import qualified Data.Param.TFVec as V

import VHDLTypes
import Constants
import Generate

mkGlobalNameTable :: [(String, (Int, Builder) )] -> NameTable
mkGlobalNameTable = Map.fromList

globalNameTable :: NameTable
globalNameTable = mkGlobalNameTable
  [ ("!"              , (2, Left $ genExprFCall exId                      ) )
  , ("replace"        , (3, Left $ genExprFCall replaceId                 ) )
  , ("head"           , (1, Left $ genExprFCall headId                    ) )
  , ("last"           , (1, Left $ genExprFCall lastId                    ) )
  , ("tail"           , (1, Left $ genExprFCall tailId                    ) )
  , ("init"           , (1, Left $ genExprFCall initId                    ) )
  , ("take"           , (2, Left $ genExprFCall takeId                    ) )
  , ("drop"           , (2, Left $ genExprFCall dropId                    ) )
  , ("+>"             , (2, Left $ genExprFCall plusgtId                  ) )
  , ("map"            , (2, Right $ genMapCall                            ) )
  , ("empty"          , (0, Left $ genExprFCall emptyId                   ) )
  , ("singleton"      , (1, Left $ genExprFCall singletonId               ) )
  , ("hwxor"          , (2, Left $ genExprOp2 AST.Xor                     ) )
  , ("hwand"          , (2, Left $ genExprOp2 AST.And                     ) )
  , ("hwor"           , (2, Left $ genExprOp2 AST.Or                      ) )
  , ("hwnot"          , (1, Left $ genExprOp1 AST.Not                     ) )
  ]
