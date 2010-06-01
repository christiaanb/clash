{-# LANGUAGE StandaloneDeriving, ExistentialQuantification, ScopedTypeVariables, TemplateHaskell, TypeOperators, TypeFamilies #-}
module Data.Param.Vector
  ( Vector
  , empty
  , (+>)
  , singleton
  , vectorTH
  , unsafeVector
  , readVector
  , length
  , lengthT
  , fromVector
  , null
  , (!)
  , replace
  , head
  , last
  , init
  , tail
  , take
  , drop
  , select
  , (<+)
  , (++)
  , map
  , zipWith
  , foldl
  , foldr
  , zip
  , unzip
  , shiftl
  , shiftr
  , rotl
  , rotr
  , concat
  , reverse
  , iterate
  , iteraten
  , generate
  , generaten
  , copy
  , copyn
  , split
  ) where
    
import Types
import Types.Data.Num
import Types.Data.Num.Decimal.Literals.TH
import Data.Param.Index

import Data.Typeable
import qualified Prelude as P
import Prelude hiding (
  null, length, head, tail, last, init, take, drop, (++), map, foldl, foldr,
  zipWith, zip, unzip, concat, reverse, iterate )
import qualified Data.Foldable as DF (Foldable, foldr)
import qualified Data.Traversable as DT (Traversable(traverse))
import Language.Haskell.TH hiding (Pred)
import Language.Haskell.TH.Syntax (Lift(..))

newtype (NaturalT s) => Vector s a = Vector {unVec :: [a]}
  deriving Eq

-- deriving instance (NaturalT s, Typeable s, Data s, Typeable a, Data a) => Data (TFVec s a)

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
vectorTH :: (Lift a) => [a] -> ExpQ
-- vectorTH xs = sigE [| (TFVec xs) |] (decTFVecT (toInteger (P.length xs)) xs)
vectorTH [] = [| empty |]
vectorTH [x] = [| singleton x |]
vectorTH (x:xs) = [| x +> $(vectorTH xs) |]

unsafeVector :: NaturalT s => s -> [a] -> Vector s a
unsafeVector l xs
  | fromIntegerT l /= P.length xs =
    error (show 'unsafeVector P.++ ": dynamic/static lenght mismatch")
  | otherwise = Vector xs

readVector :: (Read a, NaturalT s) => String -> Vector s a
readVector = read
        
-- =======================
-- = Observing functions =
-- =======================
length :: forall s a . NaturalT s => Vector s a -> Int
length _ = fromIntegerT (undefined :: s)

lengthT :: NaturalT s => Vector s a -> s
lengthT = undefined

fromVector :: NaturalT s => Vector s a -> [a]
fromVector (Vector xs) = xs

null :: Vector D0 a -> Bool
null _ = True

(!) ::  ( PositiveT s
        , NaturalT u
        , (s :>: u) ~ True) => Vector s a -> Index u -> a
(Vector xs) ! i = xs !! (fromInteger (toInteger i))

-- ==========================
-- = Transforming functions =
-- ==========================
replace :: (PositiveT s, NaturalT u, (s :>: u) ~ True) =>
  Vector s a -> Index u -> a -> Vector s a
replace (Vector xs) i y = Vector $ replace' xs (toInteger i) y
  where replace' []     _ _ = []
        replace' (_:xs) 0 y = (y:xs)
        replace' (x:xs) n y = x : (replace' xs (n-1) y)
  
head :: PositiveT s => Vector s a -> a
head = P.head . unVec

tail :: PositiveT s => Vector s a -> Vector (Pred s) a
tail = liftV P.tail

last :: PositiveT s => Vector s a -> a
last = P.last . unVec

init :: PositiveT s => Vector s a -> Vector (Pred s) a
init = liftV P.init

take :: NaturalT i => i -> Vector s a -> Vector (Min s i) a
take i = liftV $ P.take (fromIntegerT i)

drop :: NaturalT i => i -> Vector s a -> Vector (s :-: (Min s i)) a
drop i = liftV $ P.drop (fromIntegerT i)

select :: (NaturalT f, NaturalT s, NaturalT n, (f :<: i) ~ True, 
          (((s :*: n) :+: f) :<=: i) ~ True) => 
          f -> s -> n -> Vector i a -> Vector n a
select f s n = liftV (select' f' s' n')
  where (f', s', n') = (fromIntegerT f, fromIntegerT s, fromIntegerT n)
        select' f s n = ((selectFirst0 s n).(P.drop f))
        selectFirst0 :: Int -> Int -> [a] -> [a]
        selectFirst0 s n l@(x:_)
          | n > 0 = x : selectFirst0 s (n-1) (P.drop s l)
          | otherwise = []
        selectFirst0 _ 0 [] = []

(<+) :: Vector s a -> a -> Vector (Succ s) a
(<+) (Vector xs) x = Vector (xs P.++ [x])

(++) :: Vector s a -> Vector s2 a -> Vector (s :+: s2) a
(++) = liftV2 (P.++)

infixl 5 <+
infixr 5 ++

map :: (a -> b) -> Vector s a -> Vector s b
map f = liftV (P.map f)

zipWith :: (a -> b -> c) -> Vector s a -> Vector s b -> Vector s c
zipWith f = liftV2 (P.zipWith f)

foldl :: (a -> b -> a) -> a -> Vector s b -> a
foldl f e = (P.foldl f e) . unVec

foldr :: (b -> a -> a) -> a -> Vector s b -> a
foldr f e = (P.foldr f e) . unVec

zip :: Vector s a -> Vector s b -> Vector s (a, b)
zip = liftV2 P.zip

unzip :: Vector s (a, b) -> (Vector s a, Vector s b)
unzip (Vector xs) = let (a,b) = P.unzip xs in (Vector a, Vector b)

shiftl :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
          Vector s a -> a -> Vector s a
shiftl xs x = x +> init xs

shiftr :: (PositiveT s, NaturalT n, n ~ Pred s, s ~ Succ n) => 
          Vector s a -> a -> Vector s a
shiftr xs x = tail xs <+ x
  
rotl :: forall s a . NaturalT s => Vector s a -> Vector s a
rotl = liftV rotl'
  where vlen = fromIntegerT (undefined :: s)
        rotl' [] = []
        rotl' xs = let (i,[l]) = splitAt (vlen - 1) xs
                   in l : i 

rotr :: NaturalT s => Vector s a -> Vector s a
rotr = liftV rotr'
  where
    rotr' [] = []
    rotr' (x:xs) = xs P.++ [x] 

concat :: Vector s1 (Vector s2 a) -> Vector (s1 :*: s2) a
concat = liftV (P.foldr ((P.++).unVec) [])

reverse :: Vector s a -> Vector s a
reverse = liftV P.reverse

iterate :: NaturalT s => (a -> a) -> a -> Vector s a
iterate = iteraten (undefined :: s)

iteraten :: NaturalT s => s -> (a -> a) -> a -> Vector s a
iteraten s f x = let s' = fromIntegerT s in Vector (P.take s' $ P.iterate f x)

generate :: NaturalT s => (a -> a) -> a -> Vector s a
generate = generaten (undefined :: s)

generaten :: NaturalT s => s -> (a -> a) -> a -> Vector s a
generaten s f x = let s' = fromIntegerT s in Vector (P.take s' $ P.tail $ P.iterate f x)

copy :: NaturalT s => a -> Vector s a
copy x = copyn (undefined :: s) x

copyn :: NaturalT s => s -> a -> Vector s a
copyn s x = iteraten s id x

split :: ( NaturalT s
         -- , IsEven s ~ True
         ) => Vector s a -> (Vector (Div2 s) a, Vector (Div2 s) a)
split (Vector xs) = (Vector (P.take vlen xs), Vector (P.drop vlen xs))
  where
    vlen = round ((fromIntegral (P.length xs)) / 2)

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
    | all fitsLength possibilities = P.map toReadS possibilities
    | otherwise = error (fName P.++ ": string/dynamic length mismatch")
    where 
      fName = "Data.Param.TFVec.read"
      expectedL = fromIntegerT (undefined :: nT)
      possibilities = readVectorList str
      fitsLength (_, l, _) = l == expectedL
      toReadS (xs, _, rest) = (Vector xs, rest)
      
instance NaturalT s => DF.Foldable (Vector s) where
 foldr = foldr
 
instance NaturalT s => Functor (Vector s) where
 fmap = map

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
    readl   s = [([],0,t) | (">",t) <- lexVector s] P.++
                            [(x:xs,1+n,u) | (x,t)       <- reads s,
                                            (xs, n, u)  <- readl' t]
    readl'  s = [([],0,t) | (">",t) <- lexVector s] P.++
                            [(x:xs,1+n,v) | (",",t)   <- lex s,
                                            (x,u)     <- reads t,
                                            (xs,n,v)  <- readl' u]
    readParen' b g  = if b then mandatory else optional
      where optional r  = g r P.++ mandatory r
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
                                           
