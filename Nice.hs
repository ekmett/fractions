{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ViewPatterns #-}
import Control.Applicative
import Data.Ratio
import Data.Semigroup
import GHC.Real (Ratio((:%)))

type Z = Integer

--------------------------------------------------------------------------------
-- * Polynomials
--------------------------------------------------------------------------------

-- no zero divisors
class Num a => IntegralDomain a where
  isZero :: a -> Bool
  default isZero :: Eq a => a -> Bool
  isZero a = a == 0

instance IntegralDomain Integer
instance (IntegralDomain a, Integral a) => IntegralDomain (Ratio a)
instance IntegralDomain Float
instance IntegralDomain Double

data P a = P [a]
  deriving (Show, Eq)

instance IntegralDomain a => IntegralDomain (P a) where
  isZero (P xs) = null xs

zeroes :: Num a => Int -> [a] -> [a]
zeroes 0 xs = xs
zeroes n xs = 0 : zeroes (n-1) xs

xTimes :: Num a => P a -> P a
xTimes (P []) = P []
xTimes (P as) = P (0:as)

(*^) :: IntegralDomain a => a -> P a -> P a
a *^ P bs 
  | isZero a = P []
  | otherwise = P $ map (a*) bs

lift :: IntegralDomain a => a -> P a
lift a
  | isZero a = P []
  | otherwise = P [a]

-- evaluate a polynomial at 0
at0 :: Num a => P a -> a
at0 (P (a:_)) = a
at0 (P [])    = 0

-- evaluate using Horner's rule
at :: Num a => a -> P a -> a
at x (P as) = foldr (\a r -> a + x*r) 0 as

instance IntegralDomain a => Semigroup (P a) where
  P as <> x = foldr (\a r -> lift a + x*r) 0 as

instance IntegralDomain a => Monoid (P a) where
  mempty = P [0,1]
  mappend = (<>)

instance IntegralDomain a => Num (P a) where
  P as0 + P bs0 = P $ go 0 as0 bs0 where
    go n (a:as) (b:bs) = case a + b of
      c | isZero c  -> go (n + 1) as bs
        | otherwise -> zeroes n (c : go 0 as bs)
    go _ [] [] = []
    go n [] bs = zeroes n bs
    go n as [] = zeroes n as
  P as0 - P bs0 = P $ go 0 as0 bs0 where
    go n (a:as) (b:bs) = case a - b of
      c | isZero c  -> go (n + 1) as bs
        | otherwise -> zeroes n (c : go 0 as bs)
    go _ [] [] = []
    go n [] bs = zeroes n (map negate bs)
    go n as [] = zeroes n as
  P as0 * bs = go as0 where
    go [] = P []
    go (a:as)
      | isZero a = xTimes (go as)
      | otherwise = a *^ bs + xTimes (go as)
  negate (P as) = P (map negate as)
  abs xs = signum xs * xs
  signum (P []) = P []
  signum (P as) = P [signum (last as)]
  fromInteger 0 = P []
  fromInteger n = P [fromInteger n]

--------------------------------------------------------------------------------
-- * Extended Rationals
--------------------------------------------------------------------------------

infixl 7 :/

-- | Extended, unreduced, field of fractions
-- 
-- @
-- Q a = Frac a ∪ {∞,⊥}
-- @
--
-- @
-- ⊥ = 0 :/ 0
-- ∞ = a :/ 1, a /= 0
-- @
data Q a = a :/ a  
  deriving (Show, Functor)

mediant :: Num a => Q a -> Q a -> Q a
mediant (a :/ b) (c :/ d) = (a + c) :/ (b + d)

indeterminate :: IntegralDomain a => Q a -> Bool
indeterminate (a :/ b) = isZero a && isZero b

infinite :: IntegralDomain a => Q a -> Bool
infinite (a :/ b) = not (isZero a) && isZero b

instance (Num a, Eq a) => Eq (Q a) where
  (a :/ b) == (c :/ d) = a * d == b * c

instance (Num a, Ord a) => Ord (Q a) where
  compare (a :/ b) (c :/ d) = compare (a * d) (b * c)

instance Num a => Num (Q a) where
  a :/ b + c :/ d = (a*d+b*c) :/ (b*d)
  a :/ b - c :/ d = (a*d-b*c) :/ (b*d)
  (a :/ b) * (c :/ d) = (a*c) :/ (b*d)
  abs xs = signum xs * xs
  signum (a :/ b) = signum a :/ signum b
  fromInteger n = fromInteger n :/ 1

instance Num a => Fractional (Q a) where
  recip (a :/ b) = b :/ a
  (a :/ b) / (c :/ d) = (a*d) :/ (b*c)
  fromRational r = fromInteger (numerator r) :/ fromInteger (denominator r)

instance Integral a => Real (Q a) where
  toRational (k :/ n) = toInteger k % toInteger n -- blows up on indeterminate and infinite forms

instance Integral a => RealFrac (Q a) where
  properFraction (a :/ b) = case divMod a b of
    (q, r) -> (fromIntegral q, r :/ b)

instance IntegralDomain a => IntegralDomain (Q a) where
  isZero (a :/ b) = isZero a && not (isZero b)

--------------------------------------------------------------------------------
-- * Mobius Transformations
--------------------------------------------------------------------------------

-- | Linear fractional transformation
data M a = M a a a a
  deriving (Functor, Show)

instance Num a => Semigroup (M a) where
  M a b c d <> M e f g h = M (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)

instance Num a => Monoid (M a) where
  mempty = M 1 0 0 1
  mappend = (<>)

inv :: Num a => M a -> M a
inv (M a b c d) = M (negate d) b c (negate a)

mq :: Num a => M a -> Q a -> Q a
mq (M a b c d) (e :/ f) = (a*e+b*f) :/ (c*e+d*f)

-- |
-- @
-- bounds (M a 1 1 0) = (a, infinity)
-- @
bounds :: (Num a, Ord a) => M a -> (Q a, Q a)
bounds (M a b c d)
  | a*d > b*c = (b :/ d, a :/ c)
  | otherwise = (a :/ c, b :/ d)


-- | much tighter bounds assuming we derive from a digits of a continued fraction
--
-- @
-- cfbounds (M a 1 1 0) = (a, a+1)
-- @
cfbounds :: (Num a, Ord a) => M a -> (Q a, Q a)
cfbounds (M a b c d)
  | a*d > b*c = (m, a :/ c)
  | otherwise = (a :/ c, m)
  where
    m | c * d >= 0 = (a+b):/(c+d) -- we agree on the sign, so use the mediant
      | otherwise  = b :/ d

--------------------------------------------------------------------------------
-- * Bihomographic Transformations
--------------------------------------------------------------------------------

-- |
-- @
-- z = T a b c d e f g h
-- @
--
-- represents the function
-- 
-- @
-- z(x,y) = axy + bx + cy + d
--          -----------------
--          exy + fx + gy + d
-- @
--
-- and can be viewed as being simultaneously a homographic transformation
-- @z(x)[y]@ with coefficients in @Z[y]@:
--
-- z(x)[y] = (ay + b)x + (cy + d)
--           --------------------
--           (ey + f)x + (gy + h)
--
-- or as @z(y)[x]@ with coefficients in @Z[x]@:
--
-- z(y)[x] = (ax + c)y + (bx + d)
--           --------------------
--           (ey + g)y + (fy + h)
--
-- or in Z[y].
data T a = T a a a a a a a a
  deriving (Functor, Show)

-- | @mt f z x y = f(z(x,y))@
mt :: Num a => M a -> T a -> T a
mt (M a b c d) (T e e' f f' g g' h h') = T
  (a*e+b*g) (a*e'+b*g') (a*f+b*h) (a*f'+b*h')
  (c*e+d*g) (c*e'+d*g') (c*f+d*h) (c*f'+d*h')

-- | @tm1 z f x y = z(f(x),y) = z(f(x))[y]@
tm1 :: Num a => T a -> M a -> T a
tm1 (T a a' b b' c c' d d') (M e f g h) = T
  (a*e+b*g) (a'*e+b'*g) (a*f+b*h) (a'*f+b'*h)
  (c*e+d*g) (c'*e+d'*g) (c*f+d*h) (c'*f+d'*h)
  
-- | @tm2 z g x y = z(x,g(y)) = z(g(y))[x]@
tm2 :: Num a => T a -> M a -> T a
tm2 (T a b a' b' c d c' d') (M e f g h) = T
  (a*e+b*g) (a*f+b*h) (a'*e+b'*g) (a'*f+b'*h)
  (c*e+d*g) (c*f+d*h) (c'*e+d'*g) (c'*f+d'*h)

-- |
-- z(k/n,y) = (a(k/n) + c)y + (b(k/n) + d)
--            ----------------------------
--            (e(k/n) + g)y + (f(k/n) + h)
--          = (ka + nc)y + (kb+nd)
--            --------------------
--            (ke + ng)y + (kf+nh)
tq1 :: Num a => T a -> Q a -> M a
tq1 (T a b c d e f g h) (k :/ n) = M
  (k*a+n*c) (k*b+n*d)
  (k*e+n*g) (k*f+n*h)

-- |
-- @
-- z(x,k/n) = ax(k/n) + bx + c(k/n) + d
--            -------------------------
--            ex(k/n) + fx + g(k/n) + d
--          = (ka + nb)x + (kc + nd)
--            ----------------------
--            (ke + nf)x + (kg + nh)
-- @
tq2 :: Num a => T a -> Q a -> M a
tq2 (T a b c d e f g h) (k :/ n) = M
  (k*a+n*b) (k*c+n*d)
  (k*e+n*f) (k*g+n*h)

--------------------------------------------------------------------------------
-- * Exact Real Arithmetic
--------------------------------------------------------------------------------

-- nested linear fractional transformations
--
-- (m :* n :* ...) implies that all matrices from n onward always narrow a suitable interval.
-- Mero m n (Q r) -- gets simplified to m' :* Hurwitz n'
-- (m :* ...) = singular matrices m simplify to Q
-- we should not find a mero inside of a Hom
data LF
  = Quot {-# UNPACK #-} !(Q Z)
  | Hom {-# UNPACK #-} !(M Z) LF
  | Hurwitz {-# UNPACK #-} !(M (P Z))
  | Mero {-# UNPACK #-} !(T Z) {-# UNPACK #-} !(T (P Z)) LF
  | Bihom {-# UNPACK #-} !(T Z) LF LF
  deriving Show

-- | smart constructor to apply a homographic transformation
hom :: M Z -> LF -> LF
hom m                (Quot q)      = Quot (mq m q)
hom m                (Hom n x)     = Hom (m <> n) x
hom (fmap lift -> m) (Hurwitz o)   = hurwitz (m <> o <> inv m)
hom m                (Mero s t x)  = mero (mt m s) t x
hom m                (Bihom s x y) = bihom (mt m s) x y

-- | apply a meromorphic function
--
-- @
--    |
--    s
--   / \
--  x   t 0
--     / \
--    x   t 1
--       / .
--      x   .
--           .
-- @
mero :: T Z -> T (P Z) -> LF -> LF
-- TODO: simplify if the matrix has no x component? y component?
mero s t (Quot r) = hom (tq1 s r) (hurwitz (tq1 t (fmap lift r)))
mero s t x = Mero s t x

-- | apply a bihomographic transformation
bihom :: T Z -> LF -> LF -> LF
bihom m (Quot r) y = hom (tq1 m r) y
bihom m x (Quot r) = hom (tq2 m r) x
bihom m x y = Bihom m x y

-- smart constructor
hurwitz :: M (P Z) -> LF
hurwitz (fmap at0 -> M a b c d) | a*d == c*b = Quot (a :/ c)
hurwitz m = Hurwitz m

-- extract a partial quotient
quotient :: LF -> Maybe (Z, LF)
quotient (Quot (k :/ n)) = case quotRem k n of
  (q, r) -> Just (q, Quot (n :/ r))
quotient (Hom (M a b 0 0) xs) = Nothing -- infinity
quotient (Hom m@(M a b c d) xs) 
  | c /= 0, d /= 0
  , signum c * signum (c + d) > 0
  , q <- quot a c
  , q == quot b d
  , n <- cf q = Just (q, Hom (inv n <> m) xs)
quotient (Hom m xs) = quotient (hom m xs)
quotient _ = undefined
-- TODO: finish this
  
instance Eq LF

instance Ord LF

instance Num LF where
  (+) = bihom $ T 0 1 1 0 0 0 0 1
  (-) = bihom $ T 0 1 (-1) 0 0 0 0 1
  (*) = bihom $ T 1 0 0 0 0 0 0 1
  negate = hom $ M (-1) 0 0 1
  abs xs | xs < 0 = negate xs
         | otherwise = xs
  signum xs = Quot $ (case compare xs 0 of LT -> -1; EQ -> 0; GT -> 1) :/ 1
  fromInteger n = Quot $ fromInteger n :/ 1
   
instance Fractional LF where
  (/) = bihom $ T 0 1 0 0 0 0 1 0
  recip = hom $ M 0 1 1 0
  fromRational (k :% n) = Quot $ fromInteger k :/ fromInteger n

instance Floating LF where
  pi = M 0 4 1 0 `hom` hurwitz (M (P [1,2]) (P [1,2,1]) 1 0)
  exp = mero (T 1 1 2 0 (-1) 1 2 0) (T 0 1 (P [6,4]) 0 1 0 0 0)

sqrt2 :: LF
sqrt2 = cf 1 `hom` hurwitz (M 2 1 1 0)

--------------------------------------------------------------------------------
-- * Continued Fractions
--------------------------------------------------------------------------------

-- continued fraction digit
cf :: Num a => a -> M a
cf a = M a 1 1 0

-- generalized continued fraction digit
gcf :: Num a => a -> a -> M a
gcf a b = M a b 1 0

--------------------------------------------------------------------------------
-- * Redundant Binary Representation
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * Decimal
--------------------------------------------------------------------------------
