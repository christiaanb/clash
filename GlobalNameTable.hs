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
  , ("head"           , (1, genExprFCall headId                           ) )
  , ("hwxor"          , (2, genExprOp2 AST.Xor                            ) )
  , ("hwand"          , (2, genExprOp2 AST.And                            ) )
  , ("hwor"           , (2, genExprOp2 AST.And                            ) )
  , ("hwnot"          , (1, genExprOp1 AST.Not                            ) )
  ]
