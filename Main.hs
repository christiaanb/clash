module Main where

import Translator

main = do
  makeVHDL "Adders.hs" "highordtest" True