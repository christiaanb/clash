module Main where

import Translator

main = do
  makeVHDL "Alu.hs" "exec" True