{-# LANGUAGE TemplateHaskell, Arrows #-}

module FIR where

import CLasH.HardwareTypes

type Word = Signed D16

dotp as bs z = vfoldl (+) z (vzipWith (*) as bs)

fir hs pxs x = (x +>> pxs, dotp pxs hs 0)

fir4A :: State (Vector D4 Word) -> Word -> (State (Vector D4 Word), Word)
fir4A (State xs) x = (State xs', y)
  where
    (xs',y) = fir $(vTH [2,3,-2,(8::Word)]) xs x

{-# ANN fir4 TopEntity #-}
fir4 :: Comp Word Word
fir4 = proc x -> do
  y <- fir4A ^^^ (vcopy 0) -< x
  returnA -< y

{-# ANN testinp TestInput #-}
testinp = [2,3,-2,(8::Word)]
