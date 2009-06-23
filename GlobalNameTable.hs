{-# LANGUAGE TemplateHaskell #-}

module GlobalNameTable (globalNameTable) where

import Language.Haskell.TH
import qualified Data.Map as Map

import qualified ForSyDe.Backend.VHDL.AST as AST
import qualified Data.Param.TFVec as V

import VHDLTypes
import Constants
import Generate

mkGlobalNameTable :: [(String, (Int, [AST.Expr] -> AST.Expr ) )] -> NameTable
mkGlobalNameTable = Map.fromList

globalNameTable :: NameTable
globalNameTable = mkGlobalNameTable
  [ ("!"              , (2, genExprFCall exId                             ) )
  , ("replace"        , (3, genExprFCall replaceId                        ) )
  , ("head"           , (1, genExprFCall headId                           ) )
  , ("last"           , (1, genExprFCall lastId                           ) )
  , ("tail"           , (1, genExprFCall tailId                           ) )
  , ("init"           , (1, genExprFCall initId                           ) )
  , ("take"           , (2, genExprFCall takeId                           ) )
  , ("drop"           , (2, genExprFCall dropId                           ) )
  , ("hwxor"          , (2, genExprOp2 AST.Xor                            ) )
  , ("hwand"          , (2, genExprOp2 AST.And                            ) )
  , ("hwor"           , (2, genExprOp2 AST.Or                             ) )
  , ("hwnot"          , (1, genExprOp1 AST.Not                            ) )
  ]
