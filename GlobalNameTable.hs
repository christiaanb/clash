{-# LANGUAGE TemplateHaskell #-}

module GlobalNameTable (globalNameTable) where

import Language.Haskell.TH
import qualified Data.Map as Map

import qualified ForSyDe.Backend.VHDL.AST as AST
import qualified Data.Param.TFVec as V

import VHDLTypes
import Constants
import Generate

mkGlobalNameTable :: [(String, (Int, BuiltinBuilder) )] -> NameTable
mkGlobalNameTable = Map.fromList

globalNameTable :: NameTable
globalNameTable = mkGlobalNameTable
  [ (exId             , (2, genFCall                ) )
  , (replaceId        , (3, genFCall                ) )
  , (headId           , (1, genFCall                ) )
  , (lastId           , (1, genFCall                ) )
  , (tailId           , (1, genFCall                ) )
  , (initId           , (1, genFCall                ) )
  , (takeId           , (2, genFCall                ) )
  , (dropId           , (2, genFCall                ) )
  , (plusgtId         , (2, genFCall                ) )
  , (mapId            , (2, genMap                  ) )
  , (zipWithId        , (3, genZipWith              ) )
  , (foldlId          , (3, genFoldl                ) )
  , (emptyId          , (0, genFCall                ) )
  , (singletonId      , (1, genFCall                ) )
  , (copyId           , (2, genFCall                ) )
  , (hwxorId          , (2, genOperator2 AST.Xor    ) )
  , (hwandId          , (2, genOperator2 AST.And    ) )
  , (hworId           , (2, genOperator2 AST.Or     ) )
  , (hwnotId          , (1, genOperator1 AST.Not    ) )
  ]
