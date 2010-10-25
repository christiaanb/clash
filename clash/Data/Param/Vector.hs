{-# LANGUAGE TemplateHaskell, ExistentialQuantification, TypeOperators, TypeFamilies, ScopedTypeVariables #-}
module Data.Param.Vector
  ( Vector
  , empty
  , (+>)
  , singleton
  , vTH
  , unsafeVector
  , readVector
  , vlength
  , vlengthT
  , fromVector
  , vnull
  , (!)
  , vreplace
  , vhead
  , vlast
  , vinit
  , vtail
  , vtake
  , vdrop
  , vselect
  , (<+)
  , (<++>)
  , vmap
  , vzipWith
  , vfoldl
  , vfoldr
  , vzip
  , vunzip
  , (+>>)
  , (<<+)
  , vrotl
  , vrotr
  , vconcat
  , vreverse
  , viterate
  , viteraten
  , vgenerate
  , vgeneraten
  , vcopy
  , vcopyn
  , vsplit
  ) where
    
import Types
import Types.Data.Num
import Types.Data.Num.Decimal.Literals.TH
import Data.Param.Index

import Data.Typeable
import qualified Data.Foldable as DF
import qualified Data.Traversable as DT
import Language.Haskell.TH hiding (Pred)
import Language.Haskell.TH.Syntax (Lift(..))

newtype (NaturalT s) => Vector s a = Vector {unVec :: [a]}
  deriving Eq

-- ==========================
-- = Constructing functions =
-- ==========================
                                                  
empty :: Vector D0 a
empty = Vector []

(+>) :: a -> Vector s a -> Vector (Succ s) a
x +> (Vector xs) = Vector (x:xs)

infix 5 +>

singleton :: a -> Vector D1 a
singleton x = x +> empty

-- FIXME: Not the most elegant solution... but it works for now in clash
vTH :: (Lift a) => [a] -> ExpQ
-- vectorTH xs = sigE [| (TFVec xs) |] (decTFVecT (toInteger (P.length xs)) xs)
vTH []     = [| empty |]
vTH [x]    = [| singleton x |]
vTH (x:xs) = [| x +> $(vTH xs) |]

unsafeVector :: NaturalT s => s -> [a] -> Vector s a
unsafeVector l xs
  | fromIntegerT l /= length xs =
    error (show 'unsafeVector ++ ": dynamic/static lenght mismatch")
  | otherwise = Vector xs

readVector :: (Read a, NaturalT s) => String -> Vector s a
readVector = read
        
-- =======================
-- = Observing functions =
-- =======================
vlength :: forall s a . NaturalT s => Vector s a -> Int
vlength _ = fromIntegerT (undefined :: s)

vlengthT :: NaturalT s => Vector s a -> s
vlengthT = undefined

fromVector :: NaturalT s => Vector s a -> [a]
fromVector (Vector xs) = xs

vnull :: Vector D0 a -> Bool
vnull _ = True

(!) :: PositiveT s => Vector s a -> Index s -> a
(Vector xs) ! i = xs !! (fromInteger (toInteger i))

-- ==========================
-- = Transforming functions =
-- ==========================
vreplace :: PositiveT s =>
  Vector s a -> Index s -> a -> Vector s a
vreplace (Vector xs) i y = Vector $ replace' xs (toInteger i) y
  where replace' []     _ _ = []
        replace' (_:xs) 0 y = (y:xs)
        replace' (x:xs) n y = x : (replace' xs (n-1) y)
  
vhead :: PositiveT s => Vector s a -> a
vhead = head . unVec

vtail :: PositiveT s => Vector s a -> Vector (Pred s) a
vtail = liftV tail

vlast :: PositiveT s => Vector s a -> a
vlast = last . unVec

vinit :: PositiveT s => Vector s a -> Vector (Pred s) a
vinit = liftV init

vtake :: NaturalT i => i -> Vector s a -> Vector (Min s i) a
vtake i = liftV $ take (fromIntegerT i)

vdrop :: NaturalT i => i -> Vector s a -> Vector (s :-: (Min s i)) a
vdrop i = liftV $ drop (fromIntegerT i)

vselect :: (NaturalT f, NaturalT s, NaturalT n, (f :<: i) ~ True, 
           (((s :*: n) :+: f) :<=: i) ~ True) => 
           f -> s -> n -> Vector i a -> Vector n a
vselect f s n = liftV (select' f' s' n')
  where (f', s', n') = (fromIntegerT f, fromIntegerT s, fromIntegerT n)
        select' f s n = ((selectFirst0 s n).(drop f))
        selectFirst0 :: Int -> Int -> [a] -> [a]
        selectFirst0 s n l@(x:_)
          | n > 0 = x : selectFirst0 s (n-1) (drop s l)
          | otherwise = []
        selectFirst0 _ 0 [] = []

(<+) :: Vector s a -> a -> Vector (Succ s) a
(<+) (Vector xs) x = Vector (xs ++ [x])

(<++>) :: Vector s a -> Vector s2 a -> Vector (s :+: s2) a
(<++>) = liftV2 (++)

infixl 5 <+
infixr 5 <++>

vmap :: (a -> b) -> Vector s a -> Vector s b
vmap f = liftV (map f)

vzipWith :: ((s :>=: s') ~ True) => (a -> b -> c) -> Vector s a -> Vector s' b -> Vector s' c
vzipWith f = liftV2 (zipWith f)

vfoldl :: (a -> b -> a) -> a -> Vector s b -> a
vfoldl f e = (foldl f e) . unVec

vfoldr :: (b -> a -> a) -> a -> Vector s b -> a
vfoldr f e = (foldr f e) . unVec

vzip :: Vector s a -> Vector s b -> Vector s (a, b)
vzip = liftV2 zip

vunzip :: Vector s (a, b) -> (Vector s a, Vector s b)
vunzip (Vector xs) = let (a,b) = unzip xs in (Vector a, Vector b)

(+>>) :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
              a -> Vector s a -> Vector s a
x +>> xs = x +> vinit xs

(<<+) :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
              Vector s a -> a -> Vector s a
xs <<+ x = vtail xs <+ x
  
vrotl :: forall s a . NaturalT s => Vector s a -> Vector s a
vrotl = liftV rotl'
  where vlen = fromIntegerT (undefined :: s)
        rotl' [] = []
        rotl' xs = let (i,[l]) = splitAt (vlen - 1) xs
                   in l : i 

vrotr :: NaturalT s => Vector s a -> Vector s a
vrotr = liftV rotr'
  where
    rotr' [] = []
    rotr' (x:xs) = xs ++ [x] 

vconcat :: Vector s1 (Vector s2 a) -> Vector (s1 :*: s2) a
vconcat = liftV (foldr ((++).unVec) [])

vreverse :: Vector s a -> Vector s a
vreverse = liftV reverse

viterate :: NaturalT s => (a -> a) -> a -> Vector s a
viterate = viteraten (undefined :: s)

viteraten :: NaturalT s => s -> (a -> a) -> a -> Vector s a
viteraten s f x = let s' = fromIntegerT s in Vector (take s' $ iterate f x)

vgenerate :: NaturalT s => (a -> a) -> a -> Vector s a
vgenerate = vgeneraten (undefined :: s)

vgeneraten :: NaturalT s => s -> (a -> a) -> a -> Vector s a
vgeneraten s f x = let s' = fromIntegerT s in Vector (take s' $ tail $ iterate f x)

vcopy :: NaturalT s => a -> Vector s a
vcopy x = vcopyn (undefined :: s) x

vcopyn :: NaturalT s => s -> a -> Vector s a
vcopyn s x = viteraten s id x

vsplit :: ( NaturalT s
         -- , IsEven s ~ True
         ) => Vector s a -> (Vector (Div2 s) a, Vector (Div2 s) a)
vsplit (Vector xs) = (Vector (take vlen xs), Vector (drop vlen xs))
  where
    vlen = round ((fromIntegral (length xs)) / 2)

-- =============
-- = Instances =
-- =============
instance Show a => Show (Vector s a) where
  showsPrec _ = showV.unVec
    where showV []      = showString "<>"
          showV (x:xs)  = showChar '<' . shows x . showl xs
                            where showl []      = showChar '>'
                                  showl (x:xs)  = showChar ',' . shows x .
                                                  showl xs

instance (Read a, NaturalT nT) => Read (Vector nT a) where
  readsPrec _ str
    | all fitsLength possibilities = map toReadS possibilities
    | otherwise = error (fName ++ ": string/dynamic length mismatch")
    where 
      fName = "Data.Param.TFVec.read"
      expectedL = fromIntegerT (undefined :: nT)
      possibilities = readVectorList str
      fitsLength (_, l, _) = l == expectedL
      toReadS (xs, _, rest) = (Vector xs, rest)
      
instance NaturalT s => DF.Foldable (Vector s) where
 foldr = vfoldr
 
instance NaturalT s => Functor (Vector s) where
 fmap = vmap

instance NaturalT s => DT.Traversable (Vector s) where 
  traverse f = (fmap Vector).(DT.traverse f).unVec

instance (Lift a, NaturalT nT) => Lift (Vector nT a) where
  lift (Vector xs) = [|  unsafeVectorCoerse
                         $(decLiteralV (fromIntegerT (undefined :: nT)))
                          (Vector xs) |]

-- ======================
-- = Internal Functions =
-- ======================
liftV :: ([a] -> [b]) -> Vector nT a -> Vector nT' b
liftV f = Vector . f . unVec

liftV2 :: ([a] -> [b] -> [c]) -> Vector s a -> Vector s2 b -> Vector s3 c
liftV2 f a b = Vector (f (unVec a) (unVec b))

splitAtM :: Int -> [a] -> Maybe ([a],[a])
splitAtM n xs = splitAtM' n [] xs
  where splitAtM' 0 xs ys = Just (xs, ys)
        splitAtM' n xs (y:ys) | n > 0 = do
          (ls, rs) <- splitAtM' (n-1) xs ys
          return (y:ls,rs)
        splitAtM' _ _ _ = Nothing

unsafeVectorCoerse :: nT' -> Vector nT a -> Vector nT' a
unsafeVectorCoerse _ (Vector v) = (Vector v)

readVectorList :: Read a => String -> [([a], Int, String)]
readVectorList = readParen' False (\r -> [pr | ("<",s) <- lexVector r,
                                              pr <- readl s])
  where
    readl   s = [([],0,t) | (">",t) <- lexVector s] ++
                            [(x:xs,1+n,u) | (x,t)       <- reads s,
                                            (xs, n, u)  <- readl' t]
    readl'  s = [([],0,t) | (">",t) <- lexVector s] ++
                            [(x:xs,1+n,v) | (",",t)   <- lex s,
                                            (x,u)     <- reads t,
                                            (xs,n,v)  <- readl' u]
    readParen' b g  = if b then mandatory else optional
      where optional r  = g r ++ mandatory r
            mandatory r = [(x,n,u) | ("(",s)  <- lexVector r,
                                      (x,n,t) <- optional s,
                                      (")",u) <- lexVector t]

-- Custom lexer for FSVecs, we cannot use lex directly because it considers
-- sequences of < and > as unique lexemes, and that breaks nested FSVecs, e.g.
-- <<1,2><3,4>>
lexVector :: ReadS String
lexVector ('>':rest) = [(">",rest)]
lexVector ('<':rest) = [("<",rest)]
lexVector str = lex str
                                           
