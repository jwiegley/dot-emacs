module TestPrelude1  where

infix  6  &&



----------------- BOOLEANS 
data Bool = True | False
otherwise = True

not True =  False 
not False = True

True  && b = b
False && _ = False

instance Eq Bool where 
   True  == True  = True
   False == False = True
   _     == _     = False


instance Bounded Bool where
   minBound = True
   maxBound = False




------------------------------
class Eq a where
    (==), (/=) :: a -> a -> Bool

    -- Minimal complete definition: (==) or (/=)
    x == y      = not (x/=y)
    x /= y      = not (x==y)



-------------------------- ORDERING
data Ordering  = EQ | LT | GT 
instance Eq Ordering  where
   EQ == EQ = True
   LT == LT = True
   GT == GT = True
   _  == _  = False

---------------------------------------


---------------------------------------- Ints
data Int
primitive primIntEq      :: Int -> Int -> Bool
primitive intPrimBinop   :: Int -> Int -> Int
primitive primCompareInt :: Int -> Int -> Ordering

instance Eq Int where
    i1 == i2 = primIntEq i1 i2

instance Num Int where
     x + y = intPrimBinop x y 
     x * y = intPrimBinop x y
     abs x    = x
     signum x = x
instance Ord Int where
   compare x y = primCompareInt x y 
------------------------------------------



------------------------------------------- Integers
data Integer

primitive primIntegerEq      :: Integer -> Integer -> Bool
primitive integerPrimBinop   :: Integer -> Integer -> Integer
primitive primCompareInteger :: Integer -> Integer -> Ordering

instance Eq Integer where
    i1 == i2 = primIntegerEq i1 i2


instance Num Integer where
     x + y = integerPrimBinop x y 
     x * y = integerPrimBinop x y
     abs x    = x
     signum x = x

instance Ord Integer where
   compare x y = primCompareInteger x y 
------------------------------------------------


class (Eq a) => Ord a where
    compare                :: a -> a -> Ordering
    (<), (<=), (>=), (>)   :: a -> a -> Bool
    max, min               :: a -> a -> a

    -- Minimal complete definition: (<=) or compare
    -- using compare can be more efficient for complex types
    compare x y | x==y      = EQ
		| x<=y      = LT
		| otherwise = GT

    x <= y                  = compare x y /= GT
    x <  y                  = compare x y == LT
    x >= y                  = compare x y /= LT
    x >  y                  = compare x y == GT

    max x y   | x >= y      = x
	      | otherwise   = y
    min x y   | x <= y      = x
	      | otherwise   = y

class Bounded a where
    minBound, maxBound :: a
    -- Minimal complete definition: All

z = [1,2,3] == [1,2,3]


-----------------------------
class (Eq a) => Num a where
    (+), (-), (*)  :: a -> a -> a
    negate         :: a -> a
    abs, signum    :: a -> a

    -- Minimal complete definition: All, except negate or (-)
    x - y           = x + negate y
    negate x        = 0 - x



------------------------------- LIST
instance Eq a => Eq [a] where
    [] == [] = True
    (x:xs) == (y:ys) = (x==y) && (xs == ys)
    _  == _ = False


--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------

