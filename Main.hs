module Main where

import Translator

main = do
  makeVHDL "Adders.hs" "functiontest" True