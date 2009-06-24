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
  [ (exId             , (2, Left $ genExprFCall exId                      ) )
  , (replaceId        , (3, Left $ genExprFCall replaceId                 ) )
  , (headId           , (1, Left $ genExprFCall headId                    ) )
  , (lastId           , (1, Left $ genExprFCall lastId                    ) )
  , (tailId           , (1, Left $ genExprFCall tailId                    ) )
  , (initId           , (1, Left $ genExprFCall initId                    ) )
  , (takeId           , (2, Left $ genExprFCall takeId                    ) )
  , (dropId           , (2, Left $ genExprFCall dropId                    ) )
  , (plusgtId         , (2, Left $ genExprFCall plusgtId                  ) )
  , (mapId            , (2, Right $ genMapCall                            ) )
  , (zipWithId        , (3, Right $ genZipWithCall                        ) )
  , (foldlId          , (3, Right $ genFoldlCall                          ) )
  , (emptyId          , (0, Left $ genExprFCall emptyId                   ) )
  , (singletonId      , (1, Left $ genExprFCall singletonId               ) )
  , (copyId           , (2, Left $ genExprFCall copyId                    ) )
  , (hwxorId          , (2, Left $ genExprOp2 AST.Xor                     ) )
  , (hwandId          , (2, Left $ genExprOp2 AST.And                     ) )
  , (hworId           , (2, Left $ genExprOp2 AST.Or                      ) )
  , (hwnotId          , (1, Left $ genExprOp1 AST.Not                     ) )
  ]
