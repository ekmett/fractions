import Data.Function (on)
import Data.Monoid
import Data.Ratio
import Numeric.Natural
import GHC.Real

-- | The continued fraction:
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
-- CF True [a0,a1,a2,a3..an]
-- @
--
-- Only positive continued fractions can be represented this way.
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
-- CF False [a0,a1,a2,a3..an]
-- @
--
-- Coefficients a1..an are all strictly positive. a0 may be 0.
--
-- The empty list or termination of a list represents an infinite coefficient.
--
-- This is consistent with the notion that truncating a continued fraction
-- is done by adding @1 / (a_n + 1/...)@  -- which needs to be 0, which happens
-- when @a_n@ is infinity.
--
-- Note +/- 0 compare as equal, but yield different answers under `recip`.

data CF = CF Bool [Integer]
  deriving Show

infinity :: CF
infinity = CF True []

-- | The representation of a continued fraction is _almost_ unique.
--
-- Convert a continued fraction in trailing 1 form.
--
-- if e /= 1 then [a,b,c,d,e] == [a,b,c,d,e-1,1]
nf :: [Integer] -> [Integer]
nf [] = []
nf (a0:as) = go a0 as where
  go 1 [] = [1]
  go an [] = [an-1,1]
  go an (b:bs) = an : go b bs
 
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
  compare (CF True as) (CF True bs)   = cmp (nf as) (nf bs)
  compare (CF False as) (CF False bs) = cmp (nf bs) (nf as)
  compare (CF p [0]) (CF q [0]) = EQ -- +/- zero == +/- zero
  compare (CF False _) (CF True _) = LT
  compare (CF True _) (CF False _) = GT

-- | Euler's constant.
exp' :: CF
exp' = CF True $ 2:1:k 2 where k n = n:1:1:k (n + 2)

-- | The golden ratio, aka, the "most irrational number".
phi :: CF
phi = CF True ones where ones = 1:ones

continuants :: Integer -> Integer -> [Integer] -> [Integer]
continuants a b [] = []
continuants a b (c:cs) = d : continuants b d cs where d = a + b*c

numerators :: [Integer] -> [Integer]
numerators = continuants 0 1

denominators :: [Integer] -> [Integer]
denominators = continuants 1 0

convergents  :: Fractional a => CF -> [a]
convergents (CF p cs)
  = zipWith (\a b -> fromRational (tweak a:%b))
            (numerators cs)
            (denominators cs) where
  tweak
    | p         = id
    | otherwise = negate

-- the gcd of the corresponding numerators and denominators are always 1s, so we can use :%

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
data Mobius = Mobius !Integer !Integer !Integer !Integer

invert :: Mobius -> Mobius
invert (Mobius a b c d) = Mobius (-d) b c (-a)

instance Monoid Mobius where
  mempty
    = Mobius 1 0
             0 1
  Mobius a b c d `mappend` Mobius e f g h
    = Mobius
      (a*e+b*g) (a*f+b*h)
      (c*e+d*g) (c*f+d*h)

ingest :: Integer -> Mobius -> Mobius
ingest p (Mobius a b c d) = Mobius (a*p + b) a (d*p + c) c

starve :: Mobius -> Mobius
starve (Mobius _ b _ d) = Mobius b b d d

egest :: Integer -> Mobius -> Mobius
egest q (Mobius a b c d) = Mobius c d (a - c*q) (b - d*q)

-- | homographic / Mobius transformation
--
mobius :: Integer -> Integer -> Integer -> Integer -> CF -> CF
mobius a b c d (CF True xs) = CF True $ gamma (Mobius a b c d) xs -- this lies at corners
mobius a b c d (CF False xs) = CF False $ gamma

gamma :: Mobius -> [Integer] -> [Integer]
gamma m@(Mobius a b c d) xs
  | c /= 0 && d /= 0
  , q <- div a c
  , q == div b d = q : gamma (egest q m) xs
  | c == 0 && d == 0 = []
  | otherwise = case xs of
    []   -> gamma (starve m) []
    y:ys -> gamma (ingest y m) ys

instance Num CF where
  (+) = gosper 0 1 1 0 1 0 0 0    -- (x + y)/1
  (-) = gosper 0 1 (-1) 0 1 0 0 0 -- (x - y)/1
  (*) = gosper 0 0 0 1 1 0 0 0    -- (x * y)/1
  negate = mobius (-1) 0 0 1
  abs (CF _ as) = CF True as
  signum (CF p [0]) = CF p [0]
  signum (CF p _)   = CF p [1]
  fromInteger n
    | n >= 0    = CF True [n]
    | otherwise = CF False [-n]

instance Fractional CF where
  recip (CF p (0:as)) = CF p as
  recip (CF p as) = CF p (0:as)
  (/) = gosper 0 1 0 0 0 0 1 0 -- x / y
  fromRational (k :% n) = CF (k <= 0) (rat (abs k) n)

rat :: Integer -> Integer -> [Integer]
rat k n = case k `divMod` n of
  (q, r) -> q : if r == 0 then [] else rat n q

instance Enum CF where
  succ = mobius 1 1
                0 1 -- ad-bc = 1
  pred = mobius 1 (-1)
                0 1 -- ad-bc = 1
  fromEnum (CF True (n:_))  = fromIntegral n
  fromEnum (CF False (n:_)) = fromIntegral (-n)
  fromEnum (CF True [])     = maxBound
  fromEnum (CF False [])    = minBound
  toEnum = fromIntegral
