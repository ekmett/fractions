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

-- "nice integral domains" we can compre for equality: no zero divisors
class (Eq a, Num a) => IntegralDomain a where

instance IntegralDomain Integer
instance (IntegralDomain a, Integral a) => IntegralDomain (Ratio a)
instance IntegralDomain Float
instance IntegralDomain Double

data P a = P [a]
  deriving (Show, Eq)

instance IntegralDomain a => IntegralDomain (P a) where

zeroes :: Num a => Int -> [a] -> [a]
zeroes 0 xs = xs
zeroes n xs = 0 : zeroes (n-1) xs

xTimes :: Num a => P a -> P a
xTimes (P []) = P []
xTimes (P as) = P (0:as)

(*^) :: IntegralDomain a => a -> P a -> P a
0 *^ _ = 0
a *^ P bs = P $ map (a*) bs

lift :: IntegralDomain a => a -> P a
lift 0 = P []
lift a = P [a]

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
      0 -> go (n + 1) as bs
      c -> zeroes n (c : go 0 as bs)
    go _ [] [] = []
    go n [] bs = zeroes n bs
    go n as [] = zeroes n as
  P as0 - P bs0 = P $ go 0 as0 bs0 where
    go n (a:as) (b:bs) = case a - b of
      0 -> go (n + 1) as bs
      c -> zeroes n (c : go 0 as bs)
    go _ [] [] = []
    go n [] bs = zeroes n (map negate bs)
    go n as [] = zeroes n as
  P as0 * bs = go as0 where
    go [] = P []
    go (0:as) = xTimes (go as)
    go (a:as) = a *^ bs + xTimes (go as)
  negate (P as) = P (map negate as)
  abs xs = signum xs * xs
  signum (P []) = P []
  signum (P as) = P [signum (last as)]
  fromInteger 0 = P []
  fromInteger n = P [fromInteger n]

--------------------------------------------------------------------------------
-- * Extended Rationals
--------------------------------------------------------------------------------

-- | Extended, unreduced, field of fractions
-- 
-- @
-- Va = Frac a ∪ {∞,⊥}
-- @
--
-- @
-- ⊥ = V0 0
-- ∞ = Va 0, a /= 0
-- @
data V a = V a a
  deriving (Show, Functor)

mediant :: Num a => V a -> V a -> V a
mediant (V a b) (V c d) = V (a + c) (b + d)

indeterminate :: IntegralDomain a => V a -> Bool
indeterminate (V a b) = a == 0 && b == 0

infinite :: IntegralDomain a => V a -> Bool
infinite (V a b) = a /= 0 && b == 0

instance (IntegralDomain a, Eq a) => Eq (V a) where
  V a 0 == V c 0 = (a == 0) == (c == 0)
  V _ 0 == _     = False
  _     == V _ 0 = False
  V a b == V c d = a * d == b * c

instance (IntegralDomain a, Ord a) => Ord (V a) where
  compare (V a b) (V c d)
    | b * d /= 0 = compare (a * d) (b * c)
    | otherwise = hard a b c d where
      hard 0 0 0 0 = EQ
      hard 0 0 _ _ = LT
      hard _ _ 0 0 = GT
      hard _ 0 _ 0 = EQ
      hard _ 0 _ _ = GT
      hard _ _ _ _ = LT -- _ _ _ 0, really

instance IntegralDomain a => Num (V a) where
  V a b + V c d = V (if b*d == 0 then hard a b c d else a*d+b*c) (b*d) where
    hard _ _ 0 0 = 0 -- _|_ + a   = _|_
    hard 0 0 _ _ = 0 -- a + _|_   = _|_
    hard _ 0 _ 0 = 0 -- inf + inf = _|_
    hard _ _ _ _ = 1 -- inf - a   = inf
  V a b - V c d = V (if b*d == 0 then hard a b c d else a*d-b*c) (b*d) where
    hard _ _ 0 0 = 0 -- _|_ - a   = _|_
    hard 0 0 _ _ = 0 -- a - _|_   = _|_
    hard _ 0 _ 0 = 0 -- inf - inf = _|_
    hard _ _ _ _ = 1 -- inf - a   = inf
  V a b * V c d = V (if b*d == 0 then hard a b c d else a*c) (b*d) where
    hard _ _ 0 0 = 0 -- a   * _|_ = _|_
    hard 0 0 _ _ = 0 -- _|_ * a   = _|_
    hard _ 0 0 _ = 0 -- inf * 0   = _|_
    hard 0 _ _ 0 = 0 -- 0   * inf = _|_
    hard _ _ _ _ = 1 -- inf * inf = inf
  abs xs = signum xs * xs
  signum = fmap signum
  fromInteger n = V (fromInteger n) 1

instance IntegralDomain a => Fractional (V a) where
  recip (V a b) = V b a
  q@(V 0 0) / _ = q
  _ / q@(V 0 0) = q
  V _ 0 / V _ 0 = V 0 0
  q@(V _ 0) / _ = q
  V 0 _ / V 0 _ = V 0 0
  V 0 _ / _     = V 0 1
  _ / V 0 _     = undefined -- TODO finish this
{-
  V a b / V c d = V (if b*c == 0 then hard a b c d else a*d) (b*c) where
    hard 0 0 _ _ = 0 -- _|_ / x = _|_
    hard _ _ 0 0 = 0 -- x / _|_ = _|_
    hard _ 0 _ 0 = 0 -- inf / inf = _|_ 
-}
  fromRational r = V (fromInteger (numerator r)) (fromInteger (denominator r))

instance (Integral a, IntegralDomain a) => Real (V a) where
  toRational (V k n) = toInteger k % toInteger n -- blows up on indeterminate and infinite forms

instance (Integral a, IntegralDomain a) => RealFrac (V a) where
  properFraction (V a b) = case divMod a b of
    (q, r) -> (fromIntegral q, V r b)

instance IntegralDomain a => IntegralDomain (V a)

--------------------------------------------------------------------------------
-- * Mobius Transformations
--------------------------------------------------------------------------------

-- | Linear fractional transformation
data M a = M
  a a
  ---
  a a
  deriving (Functor, Show)

instance Num a => Semigroup (M a) where
  M a b c d <> M e f g h = M (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)

instance Num a => Monoid (M a) where
  mempty = M 1 0 0 1
  mappend = (<>)

inv :: Num a => M a -> M a
inv (M a b c d) = M (negate d) b c (negate a)

mv :: Num a => M a -> V a -> V a
mv (M a b c d) (V e f) = V (a*e+b*f) (c*e+d*f)

-- |
-- @
-- bounds (M a 1 1 0) = (a, infinity)
-- @
bounds :: (Num a, Ord a) => M a -> (V a, V a)
bounds (M a b c d)
  | a*d > b*c = (V b d, V a c)
  | otherwise = (V a c, V b d)


-- | much tighter bounds assuming we derive from a digits of a continued fraction
--
-- @
-- cfbounds (M a 1 1 0) = (a, a+1)
-- @
cfbounds :: (Num a, Ord a) => M a -> (V a, V a)
cfbounds (M a b c d)
  | a*d > b*c = (m, V a c)
  | otherwise = (V a c, m)
  where
    m | c * d >= 0 = V (a+b) (c+d) -- we agree on the sign, so use the mediant
      | otherwise  = V b d

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
data T a = T
  a a a a
  -------
  a a a a
  deriving (Functor, Show)

-- | @mt f z x y = f(z(x,y))@
mt :: Num a => M a -> T a -> T a
mt (M a b c d) (T e e' f f' g g' h h') = T
  (a*e+b*g) (a*e'+b*g') (a*f+b*h) (a*f'+b*h')
  -------------------------------------------
  (c*e+d*g) (c*e'+d*g') (c*f+d*h) (c*f'+d*h')

-- | @tm1 z f x y = z(f(x),y) = z(f(x))[y]@
tm1 :: Num a => T a -> M a -> T a
tm1 (T a a' b b' c c' d d') (M e f g h) = T
  (a*e+b*g) (a'*e+b'*g) (a*f+b*h) (a'*f+b'*h)
  -------------------------------------------
  (c*e+d*g) (c'*e+d'*g) (c*f+d*h) (c'*f+d'*h)
  
-- | @tm2 z g x y = z(x,g(y)) = z(g(y))[x]@
tm2 :: Num a => T a -> M a -> T a
tm2 (T a b a' b' c d c' d') (M e f g h) = T
  (a*e+b*g) (a*f+b*h) (a'*e+b'*g) (a'*f+b'*h)
  -------------------------------------------
  (c*e+d*g) (c*f+d*h) (c'*e+d'*g) (c'*f+d'*h)

-- |
-- z(k/n,y) = (a(k/n) + c)y + (b(k/n) + d)
--            ----------------------------
--            (e(k/n) + g)y + (f(k/n) + h)
--          = (ka + nc)y + (kb+nd)
--            --------------------
--            (ke + ng)y + (kf+nh)
tq1 :: Num a => T a -> V a -> M a
tq1 (T a b c d e f g h) (V k n) = M
  (k*a+n*c) (k*b+n*d)
  -------------------
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
tq2 :: Num a => T a -> V a -> M a
tq2 (T a b c d e f g h) (V k n) = M
  (k*a+n*b) (k*c+n*d)
  -------------------
  (k*e+n*f) (k*g+n*h)

-- compute the minimum and maximum of 2 elements
minmax2 :: Ord a => a -> a -> (a, a)
minmax2 x y
  | x < y     = (x, y)
  | otherwise = (x, y)

-- | best naive homographic approximation
approx :: (IntegralDomain a, Ord a) => T a -> M a
approx (T a b c d e f g h) 
  | (i,j) <- minmax2 (V a e) (V b f)
  , (k,l) <- minmax2 (V c g) (V g h)
  , V m o <- min i k
  , V n p <- max j l
  = M m n o p

--------------------------------------------------------------------------------
-- * Quadratic Fractional Transformations
--------------------------------------------------------------------------------

-- |
-- z(x) = ax^2 + bx + c
--        -------------
--        dx^2 + ex + f
--
-- or
--
-- z(x,y) = ax^2 + bxy + cy^2
--          -----------------
--          dx^2 + exy + fy^2
data Q a = Q
  a a a
  a a a
  deriving (Show, Functor)

-- z(g/h) = a(g/h)^2 + b(g/h) + c
--          ---------------------
--          d(g/h)^2 + e(g/h) + f
--        = ag^2 + bgh + ch^2
--          -----------------
--        = dg^2 + egh + eh^2

qv :: Num a => Q a -> V a -> V a
qv (Q a b c d e f) (V g h) 
  | gg <- g*g
  , gh <- g*h
  , hh <- h*h
  = V (a*gg + b*gh + c*hh) (d*gg + e*gh + f*hh)

-- z(m(x)) = a((gx+h)/(ix+j))^2 + b(gx+h)/(ix+j) + c
--           ---------------------------------------
--           d((gx+h)/(ix+j))^2 + e(gx+h)/(ix+j) + f
--         = a(gx+h)^2 + b(gx+h)(ix+j) + c(ix+j)^2
--           -------------------------------------
--           d(gx+h)^2 + e(gx+h)(ix+j) + f(ix+j)^2
--         = (agg + bgi + cii)x^2 + (2ahg + b(hi + gj) + 2cij)x  + (ahh + bhj + cjj)
--           ---------------------------------------------------------------------
--         = (dgg + egi + fii)x^2 + (2dhg + e(hi + gj) + 2fij)x  + (dhh + ehj + fjj)
qm :: Num a => Q a -> M a -> Q a
qm (Q a b c d e f) (M g h i j)
  | gg <- g*g
  , gi <- g*i
  , ii <- i*i
  , hg2 <- 2*h*g
  , hi_gj <- h*i+g*j
  , ij2 <- 2*i*j
  , hh <- h*h
  , hj <- h*j
  , jj <- j*j
  = Q
  (a*gg + b*gi + c*ii) (a*hg2 + b*hi_gj + c*ij2) (a*hh + b*hj + c*jj)
  (d*gg + e*gi + f*ii) (d*hg2 + e*hi_gj + f*ij2) (d*hh + e*hj + f*jj)
  
-- m(z(x)) = a(ex^2+fx+g) + b(hx^2+ix+j)
--           ---------------------------
--           c(ex^2+fx+g) + d(hx^2+ix+j)
--         = (ae+bh)x^2 + (af+bi)x + ag+bj
--           -----------------------------
--           (ce+dh)x^2 + (cf+di)x + cg+dj
mq :: Num a => M a -> Q a -> Q a
mq (M a b c d) (Q e f g h i j) = Q
  (a*e+b*h) (a*f+b*i) (a*g+b*j)
  (c*e+d*h) (c*f+d*i) (c*g+d*j)

--------------------------------------------------------------------------------
-- * Exact Real Arithmetic
--------------------------------------------------------------------------------

-- nested linear fractional transformations
--
-- (m :* n :* ...) implies that all matrices from n onward always narrow a suitable interval.
-- Mero m n (Quot r) -- gets simplified to m' :* Hurwitz n'
-- (m :* ...) = singular matrices m simplify to Q
-- we should not find a mero inside of a Hom
data LF
  = Quot {-# UNPACK #-} !(V Z)                              -- extended field of fractions
  | Quad {-# UNPACK #-} !(Q Z) LF                           -- delayed quadratic fractional transformation
  | Hom {-# UNPACK #-} !(M Z) LF                            -- linear fractional transformation
  | Hurwitz {-# UNPACK #-} !(M (P Z))                       -- (generalized) hurwitz numbers
  | Mero {-# UNPACK #-} !(T Z) {-# UNPACK #-} !(T (P Z)) LF -- nested bihomographic transformations
  | Bihom {-# UNPACK #-} !(T Z) LF LF                       -- bihomographic transformation
  deriving Show

-- | smart constructor to apply a homographic transformation
hom :: M Z -> LF -> LF
-- hom (Hom a _ 0 0) _             = Quot a 0
hom m                (Quot v)      = Quot (mv m v)
hom m                (Quad q x)    = Quad (mq m q) x
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
-- hurwitz (fmap at0 -> M a b c d) | a*d == c*b = Quot (V a c) -- singular: TODO: check this
hurwitz m = Hurwitz m

-- extract a partial quotient
quotient :: LF -> Maybe (Z, LF)
quotient (Quot (V k n)) = case quotRem k n of
  (q, r) -> Just (q, Quot (V n r))
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
  (+) = bihom $ T
    0 1 1 0
    0 0 0 1
  (-) = bihom $ T
    0 1 (-1) 0
    0 0 0    1
  (*) = bihom $ T
    1 0 0 0
    0 0 0 1
  negate = hom $ M
    (-1) 0
    0    1
  abs xs | xs < 0 = negate xs
         | otherwise = xs
  signum xs = Quot (V (case compare xs 0 of LT -> -1; EQ -> 0; GT -> 1) 1)
  fromInteger n = Quot (V (fromInteger n) 1)
   
instance Fractional LF where
  (/) = bihom $ T
    0 1 0 0
    0 0 1 0
  recip = hom $ M
    0 1
    1 0
  fromRational (k :% n) = Quot $ V (fromInteger k) (fromInteger n)

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
