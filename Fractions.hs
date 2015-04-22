{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MagicHash #-}
import Control.Applicative
import Data.Bits
import Data.Foldable
import Data.Ratio
import Data.Semigroup
import GHC.Real (Ratio((:%)))
import GHC.Types (Int(..))
import GHC.Integer.Logarithms
import Prelude hiding (foldr)

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
-- V a = Frac a ∪ {∞,⊥}
-- @
--
-- @
-- ⊥ = V 0 0
-- ∞ = V a 0, a /= 0
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
  V a b == V c d = b /= 0 && d /= 0 && a*d == b*c
  V a b /= V c d = b /= 0 && d /= 0 && a*d /= b*c

instance (IntegralDomain a, Ord a) => Ord (V a) where
  compare (V a b) (V c d)
    | b * d == 0 = GT -- undefined
    | otherwise = compare (a * d) (b * c)
  V a b <= V c d = b * d /= 0 && a*d <= b*c
  V a b <  V c d = b * d /= 0 && a*d <  b*c
  V a b >  V c d = b * d /= 0 && a*d >  b*c
  V a b >= V c d = b * d /= 0 && a*d >= b*c
  min u@(V a b) v@(V c d)
    | b * d == 0 = V (hard a b c d) 0
    | a*d <= b*c = u
    | a*d <= b*c = v
    where -- min ∞ ∞ = ∞, min ∞ a = ⊥, min ∞ b = ⊥
      hard 0 0 _ _ = 0
      hard _ _ 0 0 = 0
      hard _ 0 _ _ = 0
      hard _ _ _ 0 = 0
      hard _ _ _ _ = 1 -- min ∞ ∞ = ∞
  max u@(V a b) v@(V c d)
    | b * d == 0 = V (hard a b c d) 0
    | a*d <= b*c = v
    | a*d <= b*c = u
    where -- max ∞ ∞ = ∞, max ∞ a = ⊥, max ∞ b = ⊥
      hard 0 0 _ _ = 0
      hard _ _ 0 0 = 0
      hard _ 0 _ _ = 0
      hard _ _ _ 0 = 0
      hard _ _ _ _ = 1 -- max ∞ ∞ = ∞

minmax :: (IntegralDomain a, Ord a) => V a -> V a -> (V a, V a)
minmax u@(V a b) v@(V c d)
  | b * d == 0, w <- V (hard a b c d) 0 = (w,w)
  | a*d <= b*c = (u,v)
  | a*d <= b*c = (v,u)
  where -- max ∞ ∞ = ∞, max ∞ a = ⊥, max ∞ b = ⊥
    hard 0 0 _ _ = 0
    hard _ _ 0 0 = 0
    hard _ 0 _ _ = 0
    hard _ _ _ 0 = 0
    hard _ _ _ _ = 1 -- max ∞ ∞ = ∞

instance IntegralDomain a => Num (V a) where
  V a b + V c d = V (if b*d == 0 then hard a b c d else a*d+b*c) (b*d) where
    hard _ _ 0 0 = 0 -- ⊥ + a = ⊥
    hard 0 0 _ _ = 0 -- a + ⊥ = ⊥
    hard _ 0 _ 0 = 0 -- ∞ + ∞ = ⊥
    hard _ _ _ _ = 1 -- ∞ - a = ∞ 
                     -- a - ∞ = ∞
    
  V a b - V c d = V (if b*d == 0 then hard a b c d else a*d-b*c) (b*d) where
    hard _ _ 0 0 = 0 -- ⊥ - a = ⊥
    hard 0 0 _ _ = 0 -- a - ⊥ = ⊥
    hard _ 0 _ 0 = 0 -- ∞ - ∞ = ⊥
    hard _ _ _ _ = 1 -- ∞ - a = ∞
                     -- a - ∞ = ∞

  V a b * V c d = V (if b*d == 0 then hard a b c d else a*c) (b*d) where
    hard _ _ 0 0 = 0 -- a * ⊥ = ⊥
    hard 0 0 _ _ = 0 -- ⊥ * a = ⊥
    hard _ 0 0 _ = 0 -- ∞ * 0 = ⊥
    hard 0 _ _ 0 = 0 -- 0 * ∞ = ⊥
    hard _ _ _ _ = 1 -- ∞ * ∞ = ∞

  abs xs = signum xs * xs
  signum = fmap signum
  fromInteger n = V (fromInteger n) 1

-- |
-- @
-- recip ⊥ = ⊥
-- recip ∞ = 0
-- recip 0 = ∞
-- recip (V a b) = V b a
-- @
instance IntegralDomain a => Fractional (V a) where
  recip (V a b) = V b a
  p / q = p * recip q
  fromRational r = V (fromInteger (numerator r)) (fromInteger (denominator r))

instance (Integral a, IntegralDomain a) => Real (V a) where
  toRational (V k n) = toInteger k % toInteger n -- blows up on indeterminate and ∞ forms

instance (Integral a, IntegralDomain a) => RealFrac (V a) where
  properFraction (V a b) = case divMod a b of
    (q, r) -> (fromIntegral q, V r b)

-- for rescaling V,M,T,Q

integerLog2 :: Integer -> Int
integerLog2 i = I# (integerLog2# i)

-- divide out all residual powers of 2
scale :: (Foldable f, Functor f) => f Z -> f Z
scale xs
  | m <- foldl' (.|.) 0 xs
  , s <- integerLog2 (m .&. negate m) = fmap (`unsafeShiftR` s) xs

{-
-- determine the minimum bit set across all
scale :: (Foldable f, Functor f) => f Z -> f Z
scale t 
  | bs == 0 = t -- this thing is all 0's leave it alone
  | -- find the first bit by fibonacci search
  where
    bs = getOr (foldMap Or t)
    lsb = bs .&. -bs
  | any (`testBit` 0) = t
  | otherwise = fmap (`unsafeShiftR` 1) t
-}

instance IntegralDomain a => IntegralDomain (V a)

data I
  = U             -- the entire universe R∞
  | I (V Z) (V Z) -- a closed interval

class Columns f where
  columns :: Semigroup m => (V a -> m) -> f a -> m
{-
  info :: f Z -> Maybe (V Z, V Z)
  info = interval (list
 
bottom :: Columns f => f Z -> Bool
bottom = columns $ \(V a b) -> columns $ \(V c d) -> Any (u 

interval :: f Z -> I 
interval xs
  | bottom xs = U
  | otherwise = 
-}




instance Columns V where
  columns f v = f v

{-
info :: Columns f => f a -> Maybe (V a, V a)
info v = Just (v,v)
-}


sigma :: V Z -> Z
sigma (V a b) = case compare a 0 of
  LT | b <= 0 -> -1
  GT | b >= 0 -> 1
  _           -> signum b

-- | Is V ∈ V⁺ ?
--
-- @
-- posV v = sigma v /= 0
-- @
posV :: V Z -> Bool
posV (V a b) = case compare a 0 of
  LT -> b <= 0
  EQ -> b /= 0
  GT -> b >= 0

--------------------------------------------------------------------------------
-- * Mobius Transformations
--------------------------------------------------------------------------------

-- | Linear fractional transformation
data M a = M
  a a
  ---
  a a
  deriving (Functor, Show)

instance Columns M where
  columns f (M a b c d) = f (V a c) <> f (V b d)

-- | is m ∈ M⁺ ?
posM :: M Z -> Bool
posM (M a b c d) = sigma (V a c) * sigma (V b d) == 1

trace :: Num a => M a -> a
trace (M a _ _ d) = a + d

-- characteristic polynomial of M
charM :: Num a => M a -> P a
charM m = P [det m,trace m,1]

-- | Compute the invariance in the (needlessly extended) field of fractions of the coefficients.
-- of a non-singular matrix m.
--
-- @
-- invariance m = (trace m)^2 / det m
-- @
invariance :: IntegralDomain a => M a -> V a
invariance (M a b c d)
  | ad <- a*d
  , bc <- b*c
  = V (ad*ad) (ad-bc)

conjugate :: IntegralDomain a => M a -> M a -> Bool
conjugate m n 
  | i <- invariance m
  = i /= 4 && i == invariance n

-- | m ∈ M⁺ ∩ M* ?
unsignedM :: M Z -> Bool
unsignedM (M 0 _ 0 _) = False
unsignedM (M _ 0 _ 0) = False
unsignedM (M a b c d) = a >= 0 && b >= 0 && c >= 0 && d >= 0

-- | @order m == Just n@ means @mtimes n m = mempty@
order :: IntegralDomain a => M a -> Maybe Int
order m = case invariance m of
  0 -> Just 2
  1 -> Just 3
  2 -> Just 4
  3 -> Just 6
  4 -> Just 1
  _ -> Nothing

-- | rotation by pi/2
--
-- @{mempty, sinf, sneg, szer}@ is a finite cyclic group of order 4 generated by 'sinf' or 'szer'
--
-- >>> order sinf == Just 4
-- True
--
-- @
-- mempty([0,∞]) = [0,∞]
-- sinf([0,∞]) = [1,-1]
-- sneg([0,∞]) = [∞,0]
-- szer([0,∞]) = [-1,1]
-- @
sinf :: Num a => M a
sinf = M 1 1 (-1) 1

-- | rotation by pi
--
-- >>> order sneg == Just 2
-- True
--
-- >>> sneg == sinf <> sinf
-- True
sneg :: Num a => M a
sneg = M 0 1 (-1) 0

-- | rotation by 3pi/2
--
-- >>> order szer == Just 4
-- True
--
-- >>> szer == sinf <> sinf <> sinf
-- True
szer :: Num a => M a
szer = M 1 (-1) 1 1

-- 
-- @{mempty, sh, sl}@ forms a finite cyclic group of order 3 generated by 'sh' or 'sl'
--
-- @
-- x |-> 1/(1-x)
-- @
--
-- >>> order sh == Just 3
-- True
--
-- >>> sh <> sh <> sh
-- M 1 0 0 1 
--
-- @
-- mempty([0,∞]) = [0,∞]
-- sh([0,∞]) = [1,0]
-- sl([0,∞]) = [∞,1]
-- @
sh :: Num a => M a 
sh = M 0 1 (-1) 1

-- @
-- x |-> x - 1
-- @
--
-- >>> order sl == Just 3
-- True
--
-- >>> sl == sh <> sh
-- True
--
-- >>> sl <> sl <> sl == mempty
-- True
sl :: Num a => M a
sl = M 1 (-1) 1 0  

instance Num a => Semigroup (M a) where
  M a b c d <> M e f g h = M (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)

instance Num a => Monoid (M a) where
  mempty = M 1 0 0 1
  mappend = (<>)

-- | determinant of the matrix
--
-- @
-- det m * det n = det (m <> n)
-- @
det :: Num a => M a -> a
det (M a b c d) = a*d - b*c

-- | The "tame inverse" of a linear fractional transformation
--
--
-- @
-- inv m <> m = Hom (det m) 0 0 (det m) = mempty, given det m /= 0
-- @
inv :: Num a => M a -> M a
inv (M a b c d) = M (negate d) b c (negate a)

mv :: Num a => M a -> V a -> V a
mv (M a b c d) (V e f) = V (a*e+b*f) (c*e+d*f)

transposeM :: M a -> M a
transposeM (M a b c d) = M a c b d

-- |
-- @
-- bounds (M a 1 1 0) = (a, ∞)
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

instance Columns T where
  columns k (T a b c d e f g h) = k (V a e) <> k (V b f) <> k (V c g) <> k (V d h)

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

transposeT :: T a -> T a
transposeT (T a b c d e f g h) = T a c b d e g f h

-- | best naive homographic approximation
approx :: (IntegralDomain a, Ord a) => T a -> M a
approx (T a b c d e f g h) 
  | (i,j) <- minmax (V a e) (V b f)
  , (k,l) <- minmax (V c g) (V g h)
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
  -----
  a a a
  deriving (Show, Functor)

instance Columns Q where
  columns k (Q a b c d e f) = k (V a d) <> k (V b e) <> k (V c f)

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
  -------------------------------------------------------------------
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

data F
  = Quot    {-# UNPACK #-} !(V Z)     -- extended field of fractions
  | Hom     {-# UNPACK #-} !(M Z) F   -- linear fractional transformation
  | Hurwitz {-# UNPACK #-} !(M (P Z)) -- (generalized) hurwitz numbers
  deriving Show

instance Eq F where
  (==) = error "TODO"

instance Ord F where
  compare = error "TODO"

class Hom a where
  hom :: M Z -> a -> a

instance Hom F where
  hom m (Quot v) = Quot (mv m v)
  hom m (Hom n x) = Hom (m <> n) x -- check for efficiency
  hom (fmap lift -> m) (Hurwitz o) = hurwitz (m <> o <> inv m)

class Eff a where
  eff :: F -> a

instance Eff F where
  eff = id

data E
  = Eff F
  | Quad {-# UNPACK #-} !(Q Z) E                           -- delayed quadratic fractional transformation
  | Mero {-# UNPACK #-} !(T Z) {-# UNPACK #-} !(T (P Z)) E -- nested bihomographic transformations
  | Bihom {-# UNPACK #-} !(T Z) E E                        -- bihomographic transformation
  deriving Show

instance Eff E where
  eff = Eff

instance Hom E where
  hom m (Eff f)       = eff (hom m f)
  hom m (Quad q x)    = quad (mq m q) x
  hom m (Mero s t x)  = mero (mt m s) t x
  hom m (Bihom s x y) = bihom (mt m s) x y

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
mero :: T Z -> T (P Z) -> E -> E
-- TODO: simplify if the matrix has no x component? y component?
mero s t (Eff (Quot r)) = hom (tq1 s r) (hurwitz (tq1 t (fmap lift r)))
mero s t x = Mero s t x

-- | apply a bihomographic transformation
bihom :: T Z -> E -> E -> E
bihom m (Eff (Quot r)) y = hom (tq1 m r) y
bihom m x (Eff (Quot r)) = hom (tq2 m r) x
bihom m x y = Bihom m x y
{-# NOINLINE bihom #-}

quad :: Q Z -> E -> E
quad q (Eff (Quot v)) = Eff (Quot (qv q v))
quad (Q 0 a b 0 c d) x = hom (M a b c d) x
quad (Q a b c d e f) x
  | a*e == b*d, a*f == d*c, b*f == c*e, False = undefined
      -- TODO:
      -- we have a the 3x3 matrix that is antisymmetric and antireflexive of minor determinants of the 3x2 matrix, here we should be able to factor 
      -- to find @Q pr ps pt qr qs qt@ and do something with that fact
quad q x = Quad q x

-- smart constructor
hurwitz :: Eff f => M (P Z) -> f
-- hurwitz (fmap at0 -> M a b c d) | a*d == c*b = Quot (V a c) -- singular: TODO: check this
hurwitz m = eff $ Hurwitz m

-- extract a partial quotient
nextF :: F -> Maybe (Z, F)
nextF (Quot (V k n)) = case quotRem k n of
  (q, r) -> Just (q, Quot (V n r))
nextF (Hom (M a b 0 0) xs) = Nothing -- ∞ or ⊥
nextF (Hom m@(M a b c d) xs) 
  | c /= 0, d /= 0
  , signum c * signum (c + d) > 0 -- knuth style warmup?
  , q <- quot a c
  , q == quot b d
  , n <- cf q = Just (q, Hom (inv n <> m) xs)
nextF (Hom m xs) = nextF (hom m xs) -- fetch more
nextF (Hurwitz m) = nextF (Hom (fmap at0 m) $ Hurwitz (fmap (<> P [1,1]) m)) -- explicitly used Hom to keep it from merging back

square :: E -> E
square x = quad (Q 1 0 0 0 0 1) x

{-# RULES "bihomographic to quadratic" forall a b c d e f g h x. bihom (T a b c d e f g h) x x = quad (Q a (b+c) d e (f+g) h) x #-}

instance Eq E
instance Ord E 

instance Num E where
  x + y = bihom (T 0 1 1 0 0 0 0 1) x y
  {-# INLINE (+) #-}
  x - y = bihom (T 0 1 (-1) 0 0 0 0 1) x y
  {-# INLINE (-) #-}
  x * y = bihom (T 1 0 0 0 0 0 0 1) x y
  {-# INLINE (*) #-}
  negate x = hom (M (-1) 0 0 1) x
  abs xs | xs < 0 = negate xs
         | otherwise = xs
  signum xs = fromInteger $ case compare xs 0 of LT -> -1; EQ -> 0; GT -> 1
  fromInteger n = Eff $ Quot $ V n 1
   
instance Fractional E where
  x / y = bihom (T 0 1 0 0 0 0 1 0) x y
  recip x = hom (M 0 1 1 0) x
  fromRational (k :% n) = Eff $ Quot $ V k n

instance Floating E where
  pi = Eff $ M 0 4 1 0 `hom` hurwitz (M (P [1,2]) (P [1,2,1]) 1 0)
  exp = mero (T 1 1 2 0 (-1) 1 2 0) (T 0 1 (P [6,4]) 0 1 0 0 0)

sqrt2 :: Eff f => f
sqrt2 = eff $ cf 1 `hom` hurwitz (M 2 1 1 0)

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
