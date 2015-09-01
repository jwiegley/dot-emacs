-- Standard functions on rational numbers

module  Ratio (
    Ratio, Rational, (%), numerator, denominator, approxRational ) where
import Prelude

infixl 7  %

prec = 7 :: Int

data  (Integral a)      => Ratio a = !a :% !a  deriving (Eq)
--instance Eq a => Eq (Ratio a)
--type  Rational          =  Ratio Integer

intRat x = x % 1

instance  (Show a{-Integral a-})  => Show (Ratio a)  where
    showsPrec p (x:%y)  =  showParen (p > prec)
                               (shows x . showString " % " . shows y)

--instance Eq a => Eq (Ratio a) where  n1:%d1 == n2:%d2 = n1==n2 && d1==d2

--(%)                     :: (Integral a) => a -> a -> Ratio a
numerator, denominator  :: (Integral a) => Ratio a -> a
--approxRational          :: (RealFrac a) => a -> a -> Rational


-- "reduce" is a subsidiary function used only in this module.
-- It normalises a ratio by dividing both numerator
-- and denominator by their greatest common divisor.
--
-- E.g., 12 `reduce` 8    ==  3 :%   2
--       12 `reduce` (-8) ==  3 :% (-2)

reduce _ 0              =  error "Ratio.% : zero denominator"
reduce x y              =  (x `quot` d) :% (y `quot` d)
                           where d = gcd x y

x % y                   =  reduce (x * signum y) (abs y)

numerator (x :% _)      =  x

denominator (_ :% y)    =  y


instance  (Ord a,Num a{-Integral a-})  => Ord (Ratio a)  where
    (x:%y) <= (x':%y')  =  x * y' <= x' * y
    (x:%y) <  (x':%y')  =  x * y' <  x' * y

instance  (Num a,Integral a)  => Num (Ratio a)  {-where
    (x:%y) + (x':%y')   =  reduce (x*y' + x'*y) (y*y')
    (x:%y) * (x':%y')   =  reduce (x * x') (y * y')
    negate (x:%y)       =  (-x) :% y
    abs (x:%y)          =  abs x :% y
    signum (x:%y)       =  signum x :% 1
    fromInteger x       =  fromInteger x :% 1-}

instance  (Integral a)  => Real (Ratio a)  where
    toRational (x:%y)   =  toInteger x :% toInteger y

instance  (Ord a,Num a,Integral a)  => Fractional (Ratio a){-  where
    (x:%y) / (x':%y')   =  (x*y') % (y*x')
    recip (x:%y)        =  if x < 0 then (-y) :% (-x) else y :% x
    fromRational (x:%y) =  fromInteger x :% fromInteger y-}

{-
properFractionRatio (x:%y) = case quotRem x y of
	                      (q,r) -> (fromIntegral q, r:%y)
-}


instance  (Integral a)  => RealFrac (Ratio a) where
    properFraction (x:%y) = case quotRem x y of
	                      (q,r) -> (fromIntegral q, r:%y)

instance  (Integral a)  => Enum (Ratio a) {- where
    toEnum           =  fromIntegral
    fromEnum         =  fromInteger . truncate -- May overflow
    enumFrom         =  numericEnumFrom -- These numericEnumXXX functions
    enumFromThen     =  numericEnumFromThen -- are as defined in Prelude.hs
    enumFromTo       =  numericEnumFromTo -- but not exported from it!
    enumFromThenTo   =  numericEnumFromThenTo
-}

instance  (Read a, Integral a)  => Read (Ratio a) {- where
    readsPrec p  =  readParen (p > prec)
                              (\r -> [(x%y,u) | (x,s)   <- reads r,
                                                ("%",t) <- lex s,
                                                (y,u)   <- reads t ])
-}

approxRational x eps    =  simplest (x-eps) (x+eps)
        where simplest x y | y < x      =  simplest y x
                           | x == y     =  xr
                           | x > 0      =  simplest' n d n' d'
                           | y < 0      =  - simplest' (-n') d' (-n) d
                           | otherwise  =  0 :% 1
                                        where xr@(n:%d) = toRational x
                                              (n':%d')  = toRational y

              simplest' n d n' d'       -- assumes 0 < n%d < n'%d'
                        | r == 0     =  q :% 1
                        | q /= q'    =  (q+1) :% 1
                        | otherwise  =  (q*n''+d'') :% n''
                                     where (q,r)      =  quotRem n d
                                           (q',r')    =  quotRem n' d'
                                           (n'':%d'') =  simplest' d' r' d r
