{-# LANGUAGE TypeFamilies, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

import Data.Function (on)
import Data.Monoid
import Data.Ratio
import Numeric.Natural
import GHC.Real

-- | The simple continued fraction:
--
-- @
-- [a0;a1,a2,a3,a3..an]
-- @
--
-- that represents
--
-- @
-- a0 + 1/(a1 + 1/(a2 + 1/(a3 + .. 1/(a_n))))
-- @
--
-- is given by 
--
-- @
-- CF [a0,a1,a2,a3..an]
-- @
--
-- Coefficients @a1..an@ are all strictly positive. a0 may be 0.
--
-- However, only non-negative continued fractions can be represented this way.
--
-- Negative continued fractions
--
-- @
-- -[a0;a1,a2,a3..an]
-- @
--
-- are represented by
--
-- @
-- CF [-a0,-a1,-a2,-a3..an]
-- @
--
-- The empty list or termination of a list represents an infinite coefficient.
--
-- This is consistent with the notion that truncating a continued fraction
-- is done by adding @1 / (a_n + 1/...)@  -- which needs to be 0, which happens
-- when @a_n@ is infinity.
--
-- This yields the following invariant.
--
-- All coefficients are negative or all coefficients are positive, after a possible
-- leading zero.
--
-- This matches the defacto operation of the Mathematica ContinuedFraction[x,n] combinator
-- which actually disagrees with the MathWorld description of its operation.

newtype CF = CF { coefs :: [Integer] }
  deriving Show

infinity :: CF
infinity = CF []

class Fractional (Frac a) => HasFrac a where
  -- | The field of fractions
  type Frac a :: *
  embed :: a -> Frac a
  extract :: Frac a -> (a, a)

instance HasFrac Integer where
  type Frac Integer = Rational
  embed = fromInteger
  extract r = (numerator r, denominator r)
 
instance HasFrac Rational where
  type Frac Rational = Rational
  embed = id
  extract r = (numerator r :% 1, denominator r :% 1)

instance HasFrac CF where
  type Frac CF = CF
  embed = id
  extract r = (r, 1)

{-
-- | The representation of a continued fraction is _almost_ unique.
--
-- Convert a continued fraction in trailing 1 form.
--
-- if e > 1 then [a,b,c,d,e] == [a,b,c,d,e-1,1]
-- if e < -1 then [a,b,c,d,e] == [a,b,c,d,e+1,-1] -- ?

nf :: [Integer] -> [Integer]
nf [] = []
nf (a0:as) = case compare a0 0 of
    LT -> neg a0 as
    EQ -> 0 : nf as
    GT -> pos a0 as
  where
    neg (-1) [] = [-1]
    neg an [] = [an+1,-1]
    neg an (b:bs) = an : neg b bs
    pos 1 [] = [1]
    pos an [] = [an-1,1]
    pos an (b:bs) = an : pos b bs
-}

instance Eq CF where
  as == bs = compare as bs == EQ

cmp :: [Integer] -> [Integer] -> Ordering
cmp []     []     = EQ
cmp _      []     = LT
cmp []     _      = GT
cmp (a:as) (b:bs) = case compare a b of
  LT -> LT
  EQ -> cmp bs as -- swap sense
  GT -> GT

instance Ord CF where
  compare (CF as) (CF bs) = cmp as bs -- (nf as) (nf bs)

-- | Euler's constant.
exp' :: CF
exp' = CF $ 2:1:k 2 where k n = n:1:1:k (n + 2)

-- | The golden ratio, aka, the "most irrational number".
phi :: CF
phi = CF ones where ones = 1:ones

convergents  :: Fractional a => CF -> [a]
convergents (CF xs)
  = map (\(Mobius a _ c _) -> fromRational (a :% c))
  $ tail $ scanl ingest (Mobius 1 0 0 1) xs

-- | bihomographic transformations
--
-- @
-- z = axy + bx + cy + d
--     -----------------
--     exy + fx + gy + h
-- @

data Gosper = Gosper
  !Integer !Integer !Integer !Integer
  !Integer !Integer !Integer !Integer

gosper :: Integer -> Integer -> Integer -> Integer
       -> Integer -> Integer -> Integer -> Integer
       -> CF -> CF -> CF
gosper a b c d e f g h x y = undefined
  -- TODO:

  -- with a<->d = e<->h order
  -- ingestX a b c d e f g h p k = k (c + a*p) (d + b*p) a b (g + e*p) (h + f*p) e f
  -- ingestY a b c d e f g h p k = k (b + a*p) a (d + c*p) c (f + e*p) e (h + g*p) g
  -- ingestXfail a b c d e f g h k = k a b a b e f e f
  -- ingestYfail a b c d e f g h k = k a a c c e e g g 
  -- egest a b c d e f g h q k = k e f g h (a - q*e) (b - q*f) (c - q*g) (d - q*h)
  --
  -- ask if a/e, b/f, c/g, d/h all agree on the next term z, if so egest it
  -- Otherwise, read input from x if |b/f - a/e| > |c/g - a/e| or y otherwise.

-- | 
-- @
-- z = Mobius a b c d
-- @
-- 
-- represents an homographic equation of the form
--
-- @
-- z = ax + b
--     ------
--     cx + d
-- @
--
-- with integer coefficients, such that c /= 0.
data Mobius = Mobius Integer Integer Integer Integer
  deriving (Eq,Ord,Show,Read)

det :: Mobius -> Integer
det (Mobius a b c d) = a*d - b*c

digit :: Integer -> Mobius
digit a = Mobius a 1 1 0

invert :: Mobius -> Mobius
invert (Mobius a b c d) = Mobius (-d) b c (-a)

instance Monoid Mobius where
  mempty = Mobius 1 0 0 1
  Mobius a b c d `mappend` Mobius e f g h
    = Mobius
      (a*e+b*g) (a*f+b*h)
      (c*e+d*g) (c*f+d*h)

-- |
-- @
-- ingest m n = m <> Mobius n 1 1 0
-- @
ingest :: Mobius -> Integer -> Mobius
ingest (Mobius a b c d) p = Mobius (a*p+b) a (c*p+d) c

-- | 
-- @
-- starve m = m <> Mobius 1 1 0 0
-- @
starve :: Mobius -> Mobius
starve (Mobius a _ c _) = Mobius a a c c

-- |
-- @
-- egest n m = Mobius 0 1 1 n <> m
-- @
egest :: Integer -> Mobius -> Mobius
egest q (Mobius a b c d) = Mobius c d (a - c*q) (b - d*q)

-- | homographic / Mobius transformation
--
mobius :: Integer -> Integer -> Integer -> Integer -> CF -> CF
mobius a b c d (CF xs) = CF $ gamma (Mobius a b c d) xs

{-
hom :: Mobius 
hom (Mobius _ _ 0 0) _       = CF []
hom (Mobius _ _ 0 _) (CF []) = CF []
hom (Mobius _ _ 
-}

gamma :: Mobius -> [Integer] -> [Integer]
gamma m@(Mobius a b c d) xs
  | c /= 0 && d /= 0
  , q <- quot a c
  , q == quot b d = q : gamma (egest q m) xs
  | c == 0 && d == 0 = []
  | otherwise = case xs of
    []   -> gamma (starve m) []
    y:ys -> gamma (ingest m y) ys

instance Num CF where
  (+) = gosper 0 1 1 0 1 0 0 0    -- (x + y)/1
  (-) = gosper 0 1 (-1) 0 1 0 0 0 -- (x - y)/1
  (*) = gosper 0 0 0 1 1 0 0 0    -- (x * y)/1
  negate (CF xs)      = CF (map negate xs) -- mobius (-1) 0 0 1
  abs (CF as)         = CF (fmap abs as)
  signum (CF [])      = CF [1]
  signum (CF [0])     = CF [0]
  signum (CF (0:x:_)) = CF [signum x]
  signum (CF (x:_))   = CF [signum x]
  fromInteger n       = CF [n]

instance Fractional CF where
  recip (CF (0:as)) = CF as
  recip (CF as) = CF (0:as)
  (/) = gosper 0 1 0 0 0 0 1 0 -- x / y
  fromRational (k :% n) = CF (rat k n)

rat :: Integer -> Integer -> [Integer]
rat k 0 = []
rat k n = case k `quotRem` n of
  (q, r) -> q : if r == 0 then [] else rat n r

instance Enum CF where
  succ = mobius 1 1 0 1
{-
  succ (CF [])  = CF []
  succ (CF [0]) = CF [1]
  succ (CF (0:as))
    | head as < 0 = 1 - CF (0:map negate as) -- gosper
    | otherwise = CF (1:as)
  succ (CF (a:as)) = CF (succ a : as)
-}
  pred = mobius 1 (-1) 0 1 -- (x-1)/1
{-
  pred (CF [])  = CF []
  pred (CF [0]) = CF [-1]
  pred (CF (0:as))
    | head as > 0 = -1 - CF (0:map negate as) -- gosper case
    | otherwise = CF (-1:as)
  pred (CF (a:as)) = CF (pred a : as)
-}
  fromEnum (CF (n:_)) = fromIntegral n -- pushes toward zero, should truncate toward -inf
  fromEnum (CF [])    = maxBound
  toEnum = fromIntegral

