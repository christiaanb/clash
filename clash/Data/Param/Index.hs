{-# LANGUAGE  TypeFamilies, TypeOperators, ScopedTypeVariables, FlexibleInstances, TemplateHaskell, Rank2Types, FlexibleContexts #-}
module Data.Param.Index
  ( Index
  , fromNaturalT
  , fromUnsigned
  , rangeT
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))    
import Data.Bits
import Types
import Types.Data.Num.Decimal.Literals.TH

import Data.Param.Integer

instance NaturalT nT => Lift (Index nT) where
  lift (Index i) = sigE [| (Index i) |] (decIndexT (fromIntegerT (undefined :: nT)))

decIndexT :: Integer -> Q Type
decIndexT n = appT (conT (''Index)) (decLiteralT n)

fromNaturalT :: ( NaturalT n
                , NaturalT upper
                , (n :<=: upper) ~ True ) => n -> Index upper
fromNaturalT x = Index (fromIntegerT x)

fromUnsigned ::
  ( NaturalT nT
  , Integral (Unsigned nT)
  ) => Unsigned nT -> Index ((Pow2 nT) :-: D1)
fromUnsigned unsigned = Index (toInteger unsigned)

rangeT :: Index nT -> nT
rangeT _ = undefined

instance NaturalT nT => Eq (Index nT) where
    (Index x) == (Index y) = x == y
    (Index x) /= (Index y) = x /= y
    
instance NaturalT nT => Show (Index nT) where
    showsPrec prec n =
        showsPrec prec $ toInteger n
 
instance NaturalT nT => Ord (Index nT) where
    a `compare` b = toInteger a `compare` toInteger b 
        
instance NaturalT nT => Bounded (Index nT) where
    minBound = 0
    maxBound = Index (fromIntegerT (undefined :: nT))
        
instance NaturalT nT => Enum (Index nT) where
    succ x
       | x == maxBound  = error $ "Enum.succ{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `succ' of maxBound"
       | otherwise      = x + 1
    pred x
       | x == minBound  = error $ "Enum.succ{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `pred' of minBound"
       | otherwise      = x - 1
    
    fromEnum (Index x)
        | x > toInteger (maxBound :: Int) =
            error $ "Enum.fromEnum{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Index greater than maxBound :: Int"
        | x < toInteger (minBound :: Int) =
            error $ "Enum.fromEnum{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Index smaller than minBound :: Int"
        | otherwise =
            fromInteger x
    toEnum x
        | x > fromIntegral (maxBound :: Index nT) =
            error $ "Enum.fromEnum{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Index greater than maxBound :: Index " ++ show (fromIntegerT (undefined :: nT))
        | x < fromIntegral (minBound :: Index nT) =
            error $ "Enum.fromEnum{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Index smaller than minBound :: Index " ++ show (fromIntegerT (undefined :: nT))
        | otherwise =
            fromInteger $ toInteger x
    
instance NaturalT nT => Num (Index nT) where
    (Index a) + (Index b) =
        fromInteger $ a + b
    (Index a) * (Index b) =
        fromInteger $ a * b 
    (Index a) - (Index b) =
        fromInteger $ a - b
    fromInteger n
      | n > fromIntegerT (undefined :: nT) =
        error $ "Num.fromInteger{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to make Index larger than " ++ show (fromIntegerT (undefined :: nT)) ++ ", n: " ++ show n
    fromInteger n
      | n < 0 =
        error $ "Num.fromInteger{Index " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to make Index smaller than 0, n: " ++ show n
    fromInteger n =
        Index n
    abs s = s
    signum s
      | s == 0 =
          0
      | otherwise =
          1

instance NaturalT nT => Real (Index nT) where
    toRational n = toRational $ toInteger n

instance NaturalT nT => Integral (Index nT) where
    a `quotRem` b =
        let (quot, rem) = toInteger a `quotRem` toInteger b
        in (fromInteger quot, fromInteger rem)
    toInteger s@(Index x) = x
