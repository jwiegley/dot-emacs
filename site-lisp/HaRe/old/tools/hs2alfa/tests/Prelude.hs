module Prelude(module Prelude,module PreludeText,module PreludeList) where
import PreludeText
import PreludeList

infixr 5 :
infixr 0 $
infixr 9 .

-- For the P-Logic extension:
data Prop
--type Pred a = a->Prop

(f . g) x = f (g x)
id x = x
const x y = x
flip f x y = f y x
f $ x = f x

asTypeOf :: a->a->a
asTypeOf x = const x

data Char
data Integer
data Int
data Float
data Double

data IO a
instance Functor IO
instance Monad IO

foreign import putStr :: String -> IO ()
putStrLn s = putStr s >> putStr "\n"
print x = putStrLn (show x)

foreign import primSeq :: a -> b -> b
seq = primSeq

foreign import primError :: String -> a
error = primError
undefined = error "undefined"

type String = [Char]
data [] a = [] | a : [a] deriving (Eq,Ord)
data () = () deriving (Eq,Ord,Show)
data (,) a b = (,) a b deriving (Eq,Ord,Show)
data  (,,) a b c =  (,,) a b c 
data  (,,,) a b c d =  (,,,) a b c d
data  (,,,,) a b c d e =  (,,,,) a b c d e
data  (,,,,,) a b c d e f =  (,,,,,) a b c d e f
data  (,,,,,,) a b c d e f g =  (,,,,,,) a b c d e f g
data  (,,,,,,,) a b c d e f g h =  (,,,,,,,) a b c d e f g h


data Bool = False | True deriving (Eq,Ord,Bounded,Show)
data Maybe a = Nothing | Just a deriving (Eq,Ord)
data Either a b = Left a | Right b deriving (Eq)

not b = if b then False else True

class Functor f where
  fmap :: (a->b)->f a->f b

infixl 1 >>, >>=

class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
  (>>) :: m a -> m b -> m b
  fail :: String -> m a

  fail = error
  m1>>m2 = m1>>=const m2

sequence :: Monad m => [m a] -> m [a]
sequence
    = foldr mcons (return [])
  where
      mcons p q
	  = p >>= (\ x -> q >>= (\ y -> return (x : y)))
 
mapM :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f as = sequence (map f as)

instance Functor Maybe where
  fmap g m = case m of
	       Nothing -> Nothing
	       Just x -> Just (g x)

instance Monad Maybe where
  Just x >>= f = f x
  Nothing >>= _ = Nothing
  return x = Just x
  fail _ = Nothing
  --m1>>m2 =m1>>=const m2

instance Functor [] where fmap = map

maybe n j Nothing = n
maybe n j (Just x) = j x

class (Eq a,Show a) => Num a where
  (+),(-),(*) :: a -> a -> a
  negate           :: a -> a
  abs, signum      :: a -> a
  fromInteger :: Integer -> a

  x-y=x+negate y
  negate x = 0-x

class  (Num a) => Fractional a  where
    (/)              :: a -> a -> a
    recip            :: a -> a
    fromRational     :: Rational -> a

        -- Minimal complete definition:
        --      fromRational and (recip or (/))
    recip x          =  1 / x
    x / y            =  x * recip y

--even, odd        :: (Integral a) => a -> Bool
even n           =  n `rem` 2 == 0
odd n            =  not (even n)

infixl 6 +

fst (x,y) = x
snd (x,y) = y


infix 4 ==,/=,<,<=,>=,>

class Eq a where
  (==),(/=) :: a -> a -> Bool

  x/=y = not (x==y)
  x==y = not (x/=y)

class Eq a => Ord a where
    compare :: a -> a -> Ordering
    (<=) :: a -> a -> Bool
    min,max :: a -> a -> a

    min x y  = if x <= y then x else y
    max x y  = if x <= y then y else x

    x<=y = case compare x y of
		 LT -> True
		 EQ -> True
		 GT -> False

data Ordering = LT | EQ | GT deriving (Eq,Ord)


x>y = not (x<=y)
x>=y = y<=x
x<y = not (x>=y)

lexOrder EQ o = o
lexOrder o _ = o

class Bounded a where minBound,maxBound :: a

class Enum a where
  succ,pred      :: a
  toEnum         :: Int -> a
  fromEnum       :: a -> Int
  enumFrom       :: a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

otherwise = True

curry f x y = f (x,y)
uncurry f (x,y) = f x y


{-
eqList :: Eq a => [a]->[a]->Bool
[] `eqList` [] = True
(x:xs) `eqList` (y:ys) = (x==y) && (xs `eqList` ys)
_ `eqList` _ = False
--}
{-
instance Eq a => Eq [a] where
  --(==) = eqLista
  [] == [] = True
  (x:xs) == (y:ys) = (x==y) && (xs == ys)
  _ == _ = False
-}
--------------------------------------------------------------------------------
foreign import primIntegerEq :: Integer -> Integer -> Bool
foreign import primIntegerLte :: Integer -> Integer -> Bool
foreign import primIntegerAdd :: Integer -> Integer -> Integer
foreign import primIntegerNegate :: Integer -> Integer
foreign import primIntegerSignum :: Integer -> Integer
foreign import primIntegerAbs :: Integer -> Integer

instance Eq Integer where (==) = primIntegerEq

instance Ord Integer where (<=) = primIntegerLte
instance Num Integer where
  (+) = primIntegerAdd
  fromInteger = id
  negate = primIntegerNegate
  abs = primIntegerAbs
  signum = primIntegerSignum

instance Show Integer where show=undefined
instance Enum Integer

--------------------------------------------------------------------------------
foreign import primIntEq :: Int -> Int -> Bool
foreign import primInteger2Int :: Integer -> Int
foreign import primIntAdd :: Int -> Int -> Int
foreign import primIntNegate :: Int -> Int
foreign import primIntSignum :: Int -> Int
foreign import primIntAbs :: Int -> Int

instance Eq Int where (==) = primIntEq

instance Ord Int
instance Show Int

instance Num Int where
  (+) = primIntAdd
  negate = primIntNegate
  abs = primIntAbs
  signum = primIntSignum
  fromInteger = primInteger2Int

--------------------------------------------------------------------------------

instance Eq Char
instance Num Float
instance Show Float
instance Eq Float
instance Show Double
instance Num Double
instance Ord Double
instance Eq Double
instance Enum Int

instance Fractional Float
instance Fractional Double

--instance (Eq a,Eq b) => Eq (a,b) where
--  (a1,b1) == (a2,b2) = a1==a2 && b1==b2

infixr 3 &&
True && b = b
_ && _ = False

infixr 2 ||
False || b = b
_ || _ = True


------

data  (Integral a)      => Ratio a = !a :% !a  deriving (Eq)
type  Rational          =  Ratio Integer

class  (Real a, Enum a) => Integral a  where
    quot, rem        :: a -> a -> a
    div, mod         :: a -> a -> a
    quotRem, divMod  :: a -> a -> (a,a)
    toInteger        :: a -> Integer

        -- Minimal complete definition:
        --      quotRem, toInteger
    n `quot` d       =  q  where (q,r) = quotRem n d
    n `rem` d        =  r  where (q,r) = quotRem n d
    n `div` d        =  q  where (q,r) = divMod n d
    n `mod` d        =  r  where (q,r) = divMod n d
    divMod n d       =  if signum r == - signum d then (q-1, r+d) else qr
                        where qr@(q,r) = quotRem n d

class  (Num a, Ord a) => Real a  where
    toRational       ::  a -> Rational

class  (Real a, Fractional a) => RealFrac a  where
    properFraction   :: (Integral b) => a -> (b,a)
    truncate, round  :: (Integral b) => a -> b
    ceiling, floor   :: (Integral b) => a -> b

        -- Minimal complete definition:
        --      properFraction
    truncate x       =  m  where (m,_) = properFraction x

    round x          =  let (n,r) = properFraction x
                            m     = if r < 0 then n - 1 else n + 1
                          in case signum (abs r - 0.5) of
                                -1 -> n
                                0  -> if even n then n else m
                                1  -> m

    ceiling x        =  if r > 0 then n + 1 else n
                        where (n,r) = properFraction x

    floor x          =  if r < 0 then n - 1 else n
                        where (n,r) = properFraction x

class  (Fractional a) => Floating a  where
    pi                  :: a
    exp, log, sqrt      :: a -> a
    (**), logBase       :: a -> a -> a
    sin, cos, tan       :: a -> a
    asin, acos, atan    :: a -> a
    sinh, cosh, tanh    :: a -> a
    asinh, acosh, atanh :: a -> a

        -- Minimal complete definition:
        --      pi, exp, log, sin, cos, sinh, cosh
        --      asin, acos, atan
        --      asinh, acosh, atanh
    x ** y           =  exp (log x * y)
    logBase x y      =  log y / log x
    sqrt x           =  x ** 0.5
    tan  x           =  sin  x / cos  x
    tanh x           =  sinh x / cosh x

fromIntegral     :: (Integral a, Num b) => a -> b
fromIntegral     =  fromInteger . toInteger

instance Integral Integer where
  toInteger = id
  quotRem n d = error "quotRem not implemented yet"

instance Integral Int
instance Real Integer
instance Real Int
--instance Real Double
--instance Floating Double
--instance RealFrac Double
