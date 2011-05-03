module MMult where

-- import CλaSH specific types
import CLasH.HardwareTypes

type Word = Signed D16

vfoldl1 f xs = vfoldl f (vhead xs) (vtail xs)
dotp as bs   = vfoldl1 (+) (vzipWith (*) as bs)

{-# ANN mmult2x4_4x3 TopEntity #-}
mmult2x4_4x3 :: Vector D2 (Vector D4 Word) -> Vector D4 (Vector D3 Word) -> Vector D2 (Vector D3 Word)
mmult2x4_4x3 a b = mmult a b

mmult xss yss = vmap f xss
 where
   f xs  = vmap (xs `dotp`) colsy
   colsy = transpose yss (viterate (1+) 0)

transpose :: 
 ( PositiveT s1
 , PositiveT s2
 ) => Vector s1 (Vector s2 a) -> 
 Vector s2 (Index s2) -> 
 Vector s2 (Vector s1 a)
transpose m ixs = vmap (\x-> vmap (!x) m) ixs