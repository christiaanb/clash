{-# LANGUAGE TypeOperators, TemplateHaskell, TypeFamilies, ScopedTypeVariables, FlexibleContexts #-}

module MMult where

-- hide default prelude functions
import qualified Prelude as P

-- import CλaSH specific types
import CLasH.HardwareTypes
import CLasH.Translator.Annotations

type Word = Signed D16

foldl1 f xs = foldl f (head xs) (tail xs)
as ** bs    = foldl1 (+) (zipWith (*) as bs)

{-# ANN mmult2x4_4x3 TopEntity #-}
mmult2x4_4x3 :: Vector D2 (Vector D4 Word) -> Vector D4 (Vector D3 Word) -> Vector D2 (Vector D3 Word)
mmult2x4_4x3 a b = mmult a b

mmult xss yss = map f xss
 where
   f xs  = map (xs **) colsy
   colsy = transpose yss (iterate (1+) 0)

transpose :: 
 ( PositiveT s1
 , PositiveT s2
 ) => Vector s1 (Vector s2 a) -> 
 Vector s2 (Index s2) -> 
 Vector s2 (Vector s1 a)
transpose m ixs = map (\x-> map (!x) m) ixs