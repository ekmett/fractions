{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
-- import Data.Coerce
-- import Data.Function (on)
-- import Data.Ratio
import GHC.Real (Ratio(..))

-- | The (lazy) continued fraction:
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
-- This matches the defacto operation of the Mathematica ContinuedFraction[x,n] combinator,
-- which actually disagrees with the MathWorld description of its operation.

data CF where
  CF :: (s -> s -> Bool) -- compare two seeds, in order.
     -> (s -> Step s)    -- step and generate a new seed.
     -> s                -- current seed
     -> CF

data Step s where
  Step :: !Integer -> s -> Step s
  Skip :: s -> Step s -- for later stream fusion
  Stop :: Step s

next :: [Integer] -> Step [Integer]
next (a:as) = Step a as
next []     = Stop

steps :: Int -> (s -> Step s) -> s -> [Integer] 
steps n f s0 = go n s0 where
  go 0 _ = []
  go k s = case f s of
    Stop -> []
    Skip s' -> go (k-1) s'
    Step r s' -> r : go (k-1) s'

data Periodic 
  = Cold (Cyc Integer)
  | Hot {-# UNPACK #-} !Int [Integer] !Integer [Integer]

cf :: Cyc Integer -> CF
cf as = CF eq step (Cold as) where
  eq (Cold _)    = const False
  eq (Hot n _ _ _) = \(Hot m _ _ _) -> n == m
  step (Cold (b :+ bs))    = Step b (Cold bs)
  step (Cold (Cyc n (b:bs))) = Step b (Hot 0 bs b bs)
  step (Cold (Cyc _ []))     = Stop
  step (Hot n (b:bs) c cs) = Step b (Hot (n+1) bs c cs)
  step (Hot _ [] b bs)     = Step b (Hot 0 bs b bs)

infixr 5 :+

data Cyc a
  = a :+ Cyc a -- a + 1 / ...
  | Cyc {-# UNPACK #-} !Int [a]    -- a cyclic list

cyc :: [a] -> Cyc a
cyc xs = Cyc (length xs) xs


instance Show a => Show (Cyc a) where
  showsPrec d (a :+ as) = showParen (d > 5) $
    showsPrec 6 a . showString " :+ " . showsPrec 5 as
  showsPrec d (Cyc n as) = showParen (d > 10) $ 
    showString "Cyc " . showsPrec 11 n . showChar ' ' . showsPrec 11 as

-- | Explicitly detect periodicity with brent's teleporting tortoise
--
-- Produces a finite cycle for quadratic irrationals.
brent :: CF -> Cyc Integer
brent (CF p f s0) = case f s0 of
    Stop -> Cyc 0 []
    Skip s -> go 1 1 (p s0) s
    Step r s -> r :+ go 1 1 (p s0) s
  where
    go k n t s
      | t s = Cyc k (steps k f s) -- k counts skips, its high
      | k == n = step 0 (n*2) (p s) s
      | otherwise = step k n t s
    step k n t s = case f s of
      Stop -> Cyc 0 []
      Skip s' -> go (k+1) n t s'
      Step r s' -> r :+ go (k+1) n t s'
    
{-
    -- | t s = Cyc k (til0 k t s) -- k counts skips, its high
    | otherwise = case f s of
    Stop -> Cyc 0 []
    Skip s'  -- hey, we've been here before, so we'll get back
      | k == n    -> go 0 (n*2) (p s) s'
      | otherwise -> go (k+1) n t s'
    Step r s' -> if 
      | k == n    -> r :+ go 0 (n*2) (p s) s'
      | otherwise -> r :+ go (k+1) n t s'
-}

{-
  til0 n t s = case f s of
    Stop -> []
    Skip s'   -> til (n-1) t s'
    Step r s' -> r : til (n-1) t s'
  til n t s 
    | t s = [] 
    | n == 0 = [] 
    | otherwise = til0 n t s
-}

coefs :: CF -> [Integer]
coefs (CF _ f s0) = go s0 where
  go s = case f s of 
    Step a s' -> a : go s'
    Skip s' -> go s'
    Stop -> []

infinity :: CF
infinity = CF (\_ _ -> False) (\_ -> Stop) ()

aperiodic :: [Integer] -> CF
aperiodic = CF (\_ _ -> False) next 

-- | Euler's constant.
exp' :: CF
exp' = aperiodic $ 2:1:k 2 where k n = n:1:1:k (n + 2)

sqrt2 :: CF
sqrt2 = cf (1 :+ Cyc 1 [2])

sqrt7 :: CF
sqrt7 = cf (2 :+ Cyc 4 [1,1,1,4])

-- | The golden ratio, aka, the "most irrational number".
phi :: CF
phi = CF (\_ _ -> True) (\() -> Step 1 ()) ()

instance Show CF where
  showsPrec d c = showParen (d > 10) $
    showString "cf " . showsPrec 11 (brent c)

{-

instance Eq CF where
  as == bs = compare as bs == EQ

cmp :: Cyc Integer -> Cyc Integer -> Ordering
cmp (Cyc []) (Cyc []) = EQ
cmp _        (Cyc []) = LT
cmp (Cyc []) _        = GT
cmp (Cyc xs) (Cyc ys) == xs == ys
cmp (a :+ as) (b :+ bs) = case compare a b of
  LT -> LT
  EQ -> cmp bs as -- swap sense
  GT -> GT

instance Ord CF where
  -- TODO: normalize and check for equality with cycles
  compare as bs = cmp (coefs as) (coefs bs)

-}


-- | Compute a series of convergents, which alternate between optimal conservative approximations above and below to the actual answer, in increasing order by |denominator|, such that given the denominator any rational that lies closer to the real answer must have a larger denominator.
convergents  :: Fractional a => CF -> [a]
convergents (CF _ f s0) = go 1 0 0 1 s0 where
  go a b c d s = case f s of 
    Stop      -> []
    Skip s'   -> go a b c d s'
    Step y s'
      | k <- a*y+b
      , n <- c*y+d -> fromRational (k :% n) : go k a n c s'

-- | 
-- @
-- z = hom a b c d
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
-- with integer coefficients.
--
-- TODO: detect cycles, once we do, detect cycle length, then our position in it
-- this will let us detect the length of the cycle we emit.

data Hom s = Hom !Integer !Integer !Integer !Integer (Maybe s)

hom :: Integer -> Integer -> Integer -> Integer -> CF -> CF
hom a0 b0 c0 d0 (CF eq0 step0 s0) = CF eq step (Hom a0 b0 c0 d0 (Just s0)) where
  eq (Hom _ _ _ _ Nothing) = const False
  eq (Hom a b c d (Just s)) = let p = eq0 s in \xs -> case xs of
    Hom a' b' c' d' (Just s') -> a == a' && b == b' && c == c' && d == d' && p s'
    _ -> False
  step (Hom a b c d s) = stepHom step0 a b c d s

stepHom
  :: (s -> Step s)
  -> Integer -> Integer
  -> Integer -> Integer
  -> Maybe s -> Step (Hom s)
stepHom _ _ _ 0 0 _ = Stop
stepHom step0 a b c d ms
  | c /= 0, d /= 0
  , q <- quot a c, q == quot b d
  = Step q (Hom c d (a - c*q) (b - d*q) ms)
  | otherwise = case ms of 
     Nothing -> Skip (Hom a a c c Nothing)
     Just s -> case step0 s of
       Step y s' -> Skip (Hom (a*y+b) a (c*y+d) c (Just s'))
       Skip s' -> Skip (Hom a b c d (Just s'))
       Stop -> Skip (Hom a a c c Nothing)

data Bihom s t
  = Bihom !Integer !Integer !Integer !Integer
          !Integer !Integer !Integer !Integer (Maybe s) (Maybe t)

-- | Gosper-style bihomographic transformations
--
-- @
-- z = axy + by + cx + d
--     -----------------
--     exy + fy + gx + h
-- @
bihom :: Integer -> Integer -> Integer -> Integer
      -> Integer -> Integer -> Integer -> Integer
      -> CF -> CF -> CF
bihom a0 b0 c0 d0 e0 f0 g0 h0 (CF eq1 step1 s1) (CF eq2 step2 s2)
  = CF eq step (Bihom a0 b0 c0 d0 e0 f0 g0 h0 (Just s1) (Just s2)) where

  meq f (Just s) (Just t) = f s t
  meq _ Nothing Nothing = True
  meq _ _ _ = False

  -- we'll never repeat if we're rational
  --eq (Bihom _ _ _ _ _ _ _ _ Nothing Nothing) = \_ -> False

  -- were in the Hom case
  eq (Bihom a b _ _ e f _ _ ms Nothing) = 
    \(Bihom a' b' _ _ e' f' _ _ ms' _)
    -> a == a' && b == b' && e == e' && f == f' && meq eq1 ms ms'

  eq (Bihom a _ c _ e _ g _ Nothing mt) =
    \(Bihom a' _ c' _ e' _ g' _ _ mt')
    -> a == a' && c == c' && e == e' && g == g' && meq eq2 mt mt'

  eq (Bihom a b c d e f g h ms mt) = \(Bihom a' b' c' d' e' f' g' h' ms' mt')
    -> a == a' && b == b' && c == c' && d == d'
    && e == e' && f == f' && g == g' && h == h'
    && meq eq1 ms ms' && meq eq2 mt mt'

{-
  eq (Bihom a b c d e f g h (Just s) (Just t)) = \(Bihom a' b' c' d' e' f' g' h' ms' mt')
    -> a == a' && b == b' && c == c' && d == d'
    && e == e' && f == f' && g == g' && h == h'
    && case ms' of 
      Just s' -> eq1 s s' && case mt' of
        Just t' -> eq2 t t'
        _ -> False
      _ -> False
-}

  step (Bihom a b _ _ e f _ _ ms Nothing) = case stepHom step1 a b e f ms of
    Stop -> Stop
    Skip (Hom a' b' e' f' ms') -> Skip (Bihom a' b' 0 0 e' f' 0 0 ms' Nothing)
    Step q (Hom a' b' e' f' ms') -> Step q (Bihom a' b' 0 0 e' f' 0 0 ms' Nothing)

  step (Bihom a _ c _ e _ g _ Nothing mt) = case stepHom step2 a c e g mt of
    Stop -> Stop
    Skip (Hom a' c' e' g' mt') -> Skip (Bihom a' 0 c' 0 e' 0 g' 0 Nothing mt')
    Step q (Hom a' c' e' g' mt') -> Step q (Bihom a' 0 c' 0 e' 0 g' 0 Nothing mt')

  step (Bihom a b c d e f g h ms mt)
   | e /= 0, f /= 0, g /= 0, h /= 0 
   , q <- quot a e, q == quot b f
   , q == quot c g, q == quot d h
   = Step q (Bihom e f g h (a-q*e) (b-q*f) (c-q*g) (d-q*h) ms mt)

  step (Bihom a b c d e f g h ms@(Just s) mt@(Just t))
   | e /= 0 || f /= 0
   , (e == 0 && g == 0) || abs (g*e*b - g*a*f) > abs (f*e*c - g*a*f)
   = case step1 s of 
     Step x s' -> Skip (Bihom (a*x+b) a (c*x+d) c (e*x+f) e (g*x+h) g (Just s') mt)
     Skip s'   -> Skip (Bihom a b c d e f g h (Just s') mt)
     Stop      -> Skip (Bihom a b c d e f g h Nothing mt)
   | otherwise = case step2 t of
     Step y t' -> Skip (Bihom (a*y+c) (b*y+d) a b (e*y+g) (f*y+h) e f ms (Just t'))
     Skip t'   -> Skip (Bihom a b c d e f g h ms (Just t'))
     Stop      -> Skip (Bihom a b c d e f g h ms Nothing)

mapCF :: (Integer -> Integer) -> CF -> CF
mapCF g (CF p f s0) = CF p f' s0 where
  f' s = case f s of
    Step a s' -> Step (g a) s'
    Skip s' -> Skip s'
    Stop -> Stop

instance Num CF where
  (+) = bihom
    0 1 1 0 -- x + y
    0 0 0 1 -- 1
  (-) = bihom
    0 (-1) 1 0 -- x - y
    0 0    0 1 -- 1
  (*) = bihom
    1 0 0 0 -- xy
    0 0 0 1 -- 1
  negate = mapCF negate
  abs = mapCF abs
  signum (CF _ f s0) = CF (\_ _ -> False) step (SignumStart s0) where
    step (SignumStart s) = case f s of
      Step 0 s' -> Skip (SignumZero s')
      Step x _  -> Step (signum x) SignumDone
      Skip s'   -> Skip (SignumStart s')
      Stop -> Step 1 SignumDone
    step (SignumZero s) = case f s of
      Step x _ -> Step (signum x) SignumDone
      Skip s'  -> Skip (SignumZero s')
      Stop     -> Step 0 SignumDone
    step SignumDone = Stop
  fromInteger n = aperiodic [n]

data Signum s = SignumStart s | SignumZero s | SignumDone

instance Fractional CF where
  recip = hom 0 1 1 0 -- todo exploit the more efficient put on / take off 0 representation
  (/) = bihom
     0 0 1 0 -- x
     0 1 0 0 -- y
  fromRational (k0 :% n0) = aperiodic (go k0 n0) where
    go k 0 = []
    go k n = case k `quotRem` n of
      (q, r) -> q : if r == 0
        then []
        else go n r

instance Enum CF where
  succ = hom
    1 1 -- x + 1
    0 1 -- 1
  pred = hom
    1 (-1) -- x - 1
    0 1    -- 1
  fromEnum (CF _ f s0) = go s0 where
    go s = case f s of
      Step n _ -> fromIntegral n
      Skip s'  -> go s'
      Stop     -> maxBound
  toEnum = fromIntegral
