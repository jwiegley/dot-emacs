module Prelude where
import PreludeInt

type Int = HInt
data Integer
instance Eq Integer where (==) = primEqInteger

primEqInteger i1 i2 =
   primIntegerNeg i1==primIntegerNeg i2 &&
   primIntegerDigits i1==primIntegerDigits i2

foreign import primIntegerNeg :: Integer -> Bool
foreign import primIntegerDigits :: Integer -> [[Bool]]

foreign import primError :: String->a
error = primError
undefined = error "undefined"

--data Int
data Char
type String = [Char]

--instance Eq Int
--instance Num Int
instance Enum Int where
  succ x = x+1
  pred x = x-1
  fromEnum = id; toEnum = id
  enumFrom x = x:enumFrom (succ x)
  enumFromTo x y = enumFromThenTo x 1 y
  enumFromThen x y = x:enumFromThen (x+y) y
  enumFromThenTo x y z = if x<=y then enumUp x else enumDown x
    where enumUp x = if x<=z then x:enumUp (x+y) else []
          enumDown x = if x>=z then x:enumDown (x-y) else []

data Bool = False | True deriving (Eq,Enum,Bounded)
--data Maybe a = Nothing | Just a deriving (Eq)

data Prop
--type Pred a = a->Prop

class Eq a where
  (==),(/=) :: a -> a -> Bool
  x/=y = not (x==y)

data Ordering = LT | EQ | GT deriving (Eq)

class Ord a where
  compare :: a->a->Ordering
  (<=),(>=) :: a->a->Bool
  x>=y = compare x y/=LT
  x<=y = compare x y/=GT
  
class Bounded a where minBound,maxBound::a

instance Ord Int where
   compare x y = case signum (x-y) of
                   -1 -> LT
		   0 -> EQ
		   1 -> GT

data [] a = [] | a : [a] deriving (Eq,Ord)

map f = mapf
  where
   mapf [] = []
   mapf (x:xs) = f x:mapf xs

not False = True
not True = False

infixr 9 .
(f . g) x = f (g x)

infixr 0 $
f $ x = f x

class Eq a => Num a where
  (+),(-),(*) :: a -> a -> a
  fromInteger :: Integer -> a
  negate :: a->a
  abs,signum :: a->a
  a-b=a+negate b

subtract x y = y-x

id y = y
const x y = x
flip f x y = f y x -- Used by the type checker for sections, like (==0)

class Enum a where
  succ, pred :: a -> a
  toEnum :: Int -> a
  fromEnum :: a -> Int
  enumFrom :: a -> [a]
  enumFromThen,enumFromTo :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

  succ             =  toEnum . (+1) . fromEnum
  pred             =  toEnum . (subtract 1) . fromEnum
  enumFrom x       =  map toEnum [fromEnum x ..]
  enumFromTo x y   =  map toEnum [fromEnum x .. fromEnum y]
  enumFromThen x y =  map toEnum [fromEnum x, fromEnum y ..]
  enumFromThenTo x y z = map toEnum [fromEnum x, fromEnum y .. fromEnum z]

data (,) a b = (,) a b deriving (Eq,Ord)
data (,,) a b c = (,,) a b c -- deriving (Eq)

fst (a,b) = a
snd (a,b) = b

infixr 3 &&
x&&y = if x then y else False

lexOrder EQ o = o
lexOrder o _ = o
