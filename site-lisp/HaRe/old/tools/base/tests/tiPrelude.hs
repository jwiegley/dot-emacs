module Prelude(module Prelude,module PreludeText) where
import PreludeText

default (Int)

-- Primitive types
data Char
data Int
data Integer
data Float
data Double

data () = () deriving (Eq,Show,Bounded,Ord,Read)
data (,) a b = (,) a b deriving (Eq,Show,Bounded,Ord)
data (,,) a b c = (,,) a b c
data (,,,) a b c d = (,,,) a b c d

data (->) a b

data [] a = [] | a : [a] deriving (Eq,Show,Ord,Read)
data Bool = False | True deriving (Eq,Show,Bounded,Enum,Ord,Read)
data Either a b = Left a | Right b deriving (Eq,Show,Ord,Read)
data Maybe a = Nothing | Just a deriving (Eq,Show,Ord,Read)

type String = [Char]

undefined | False = undefined
error s = undefined

either f g (Left x) = f x
either f g (Right y) = g y

maybe n j Nothing = n
maybe n j (Just x) = j x

--foldr :: (a->b->b)->b->[a]->b
foldr c n [] = n
foldr c n (x:xs) = c x (foldr c n xs)

filter p xs = [x|x<-xs,p x]

infixr 3 &&
True && b = b
_ && _ = False

infix 4 ==,/=

class Eq a where
  (==),(/=) :: a -> a -> Bool

  a/=b = not (a==b)


not False = True
not True  = False

lexOrder EQ o = o
lexOrder o  _ = o

class (Eq a,Show a) => Num a where
  fromInteger :: Integer -> a
  fromInt :: Int -> a
  (+),(-),(*) :: a -> a -> a
  negate :: a->a
-- ...

class Enum a where
  succ, pred :: a -> a
  toEnum :: Int -> a
  fromEnum :: a -> Int
  enumFrom :: a -> [a]
  enumFromThen,enumFromTo :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

class Monad m where
  return :: a -> m a
  (>>) :: m a -> m b -> m b
  (>>=) :: m a -> (a -> m b) -> m b
  fail :: String -> m a

  --m1>>m2 = m1 >>= const m2

m2 =<< m1 = m1 >>= m2

id x = x
const x y = x
flip f x y = f y x

infixr 9 .
--(.) :: (b->c)->(a->b)->(a->c)
(f . g) x = f (g x)

instance Show Int
instance Read Int
instance Enum Int
instance Num Int
instance Enum Char
instance Eq Char
instance Eq Int
instance Ord Int

{-
instance Eq Bool where
  True==True = True
  False==False = True
  _ == _ = False
-}
{-
instance Eq a => Eq [a] where
  [] == [] = True
  (x:xs) == (y:ys) = (x==y) && (xs==ys)
--}
class Functor f where fmap :: (a->b) -> f a -> f b

--(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x:(xs++ys)

length :: [a]->Int
length [] = 0
length (x:xs) = 1 + length xs


--map :: (a->b)->[a]->[b]

map f = foldr ((:).f) []
concatMap f = foldr ((++).f) []

--map f [] = []
--map f (x:xs) = f x:map f xs


instance Functor [] where
  fmap = map

fst (x,y) = x
snd = \ p -> case p of
               (x,y) -> y

--until            :: (a -> Bool) -> (a -> a) -> a -> a
until p f x 
     | p x       =  x
     | otherwise =  until p f (f x)

otherwise = True

------
data World
data IO a = IO (World->(a,World)) -- for example

instance Monad IO

print x = putStrLn (show x)

foreign import putStr :: String -> IO ()
foreign import putStrLn :: String -> IO ()

class (Real a,Enum a) => Integral a where
  toInteger :: a->Integer

class (Num a,Ord a) => Real a where
  toRational :: a -> Rational

type Rational = Ratio Integer

data Ratio a = a :% a

class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<),(<=),(>=),(>) :: a -> a -> Bool

data Ordering = LT | EQ | GT deriving (Eq,Bounded,Enum,Ord,Show,Read)

class Bounded a where minBound,maxBound::a
