{-# LANGUAGE  TypeFamilies, TypeOperators, ScopedTypeVariables, FlexibleInstances, TemplateHaskell, Rank2Types, FlexibleContexts #-}
module Data.Param.Signed
  ( Signed
  , resize
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import Data.Bits
import Types
import Types.Data.Num.Decimal.Literals.TH

import Data.Param.Integer

instance NaturalT nT => Lift (Signed nT) where
  lift (Signed i) = sigE [| (Signed i) |] (decSignedT (fromIntegerT (undefined :: nT)))

decSignedT :: Integer -> Q Type
decSignedT n = appT (conT (''Signed)) (decLiteralT n)

resize :: (NaturalT nT, NaturalT nT') => Signed nT -> Signed nT'
resize a = fromInteger (toInteger a)

sizeT :: Signed nT
      -> nT
sizeT _ = undefined

mask :: forall nT . NaturalT nT
     => nT
     -> Integer
mask _ = bit (fromIntegerT (undefined :: nT)) - 1

signBit :: forall nT . NaturalT nT
        => nT
        -> Int
signBit _ = fromIntegerT (undefined :: nT) - 1

isNegative :: forall nT . NaturalT nT
           => Signed nT
           -> Bool
isNegative (Signed x) =
    testBit x $ signBit (undefined :: nT)

instance NaturalT nT => Eq (Signed nT) where
    (Signed x) == (Signed y) = x == y
    (Signed x) /= (Signed y) = x /= y

instance NaturalT nT => Show (Signed nT) where
    showsPrec prec n =
        showsPrec prec $ toInteger n

instance NaturalT nT => Read (Signed nT) where
    readsPrec prec str =
        [ (fromInteger n, str)
        | (n, str) <- readsPrec prec str ]

instance NaturalT nT => Ord (Signed nT) where
    a `compare` b = toInteger a `compare` toInteger b

instance NaturalT nT => Bounded (Signed nT) where
    minBound = Signed $ negate $ 1 `shiftL` (fromIntegerT (undefined :: nT) - 1)
    maxBound = Signed $ (1 `shiftL` (fromIntegerT (undefined :: nT) - 1)) - 1

instance NaturalT nT => Enum (Signed nT) where
    succ x
       | x == maxBound  = error $ "Enum.succ{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `succ' of maxBound"
       | otherwise      = x + 1
    pred x
       | x == minBound  = error $ "Enum.succ{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `pred' of minBound"
       | otherwise      = x - 1
    
    fromEnum (Signed x)
        | x > toInteger (maxBound :: Int) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed greater than maxBound :: Int"
        | x < toInteger (minBound :: Int) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed smaller than minBound :: Int"
        | otherwise =
            fromInteger x
    toEnum x
        | x' > toInteger (maxBound :: Signed nT) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed greater than maxBound :: Signed " ++ show (fromIntegerT (undefined :: nT))
        | x' < toInteger (minBound :: Signed nT) =
            error $ "Enum.fromEnum{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to take `fromEnum' on Signed smaller than minBound :: Signed " ++ show (fromIntegerT (undefined :: nT))
        | otherwise =
            fromInteger x'
            where x' = toInteger x

instance NaturalT nT => Num (Signed nT) where
    (Signed a) + (Signed b) =
        fromInteger $ a + b
    (Signed a) * (Signed b) =
        fromInteger $ a * b
    negate (Signed n) =
        fromInteger $ (n `xor` mask (undefined :: nT)) + 1
    a - b =
        a + (negate b)
    
    fromInteger n
      | n > 0 =
        Signed $ n .&. mask (undefined :: nT)
    fromInteger n
      | n < 0 =
        negate $ fromInteger $ negate n
    fromInteger _ =
        Signed 0
    
    abs s
      | isNegative s =
          negate s
      | otherwise =
          s
    signum s
      | isNegative s =
          -1
      | s == 0 =
          0
      | otherwise =
          1

instance NaturalT nT => Real (Signed nT) where
    toRational n = toRational $ toInteger n

instance NaturalT nT => Integral (Signed nT) where
    a `quot` b =
        fromInteger $ toInteger a `quot` toInteger b
    a `rem` b =
        fromInteger $ toInteger a `rem` toInteger b
    a `div` b =
        fromInteger $ toInteger a `div` toInteger b
    a `mod` b =
        fromInteger $ toInteger a `mod` toInteger b
    a `quotRem` b =
        let (quot, rem) = toInteger a `quotRem` toInteger b
        in (fromInteger quot, fromInteger rem)
    a `divMod` b =
        let (div, mod) = toInteger a `divMod` toInteger b
        in (fromInteger div, fromInteger mod)
    toInteger s@(Signed x) =
        if isNegative s
           then let Signed x' = negate s in negate x'
           else x

instance NaturalT nT => Bits (Signed nT) where
    (Signed a) .&. (Signed b) = Signed $ a .&. b
    (Signed a) .|. (Signed b) = Signed $ a .|. b
    (Signed a) `xor` Signed b = Signed $ a `xor` b
    complement (Signed x) = Signed $ x `xor` mask (undefined :: nT)
    (Signed x) `shiftL` b
      | b < 0 = error $ "Bits.shiftL{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to shift by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) .&. (x `shiftL` b)
    s@(Signed x) `shiftR` b
      | b < 0 = error $ "Bits.shiftR{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to shift by negative amount"
      | isNegative s =
        Signed $ mask (undefined :: nT) .&.
            ((x `shiftR` b) .|. (mask (undefined :: nT) `shiftL` (fromIntegerT (undefined :: nT) - b)))
      | otherwise =
        Signed $ (mask (undefined :: nT)) .&. (x `shiftR` b)
    (Signed a) `rotateL` b
      | b < 0 =
        error $ "Bits.rotateL{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) .&.
            ((a `shiftL` b) .|. (a `shiftR` (fromIntegerT (undefined :: nT) - b)))
    (Signed a) `rotateR` b
      | b < 0 =
        error $ "Bits.rotateR{Signed " ++ show (fromIntegerT (undefined :: nT)) ++ "}: tried to rotate by negative amount"
      | otherwise =
        Signed $ mask (undefined :: nT) .&.
            ((a `shiftR` b) .|. (a `shiftL` (fromIntegerT (undefined :: nT) - b)))
    bitSize _ = fromIntegerT (undefined :: nT)
    isSigned _ = True
