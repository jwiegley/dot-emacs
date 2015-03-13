module D6 where
data Tree a = Leaf a | Branch (Tree a) (Tree a)
 
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right)
    = (myFringe left) ++ (myFringe right)
 
class SameOrNot a
  where
      isSame :: a -> a -> Bool
      isNotSame :: a -> a -> Bool
 
instance SameOrNot Int
  where
      isSame a b = a == b
      isNotSame a b = a /= b
 
sumSquares ((x : xs))
    = (sq x) + (sumSquares xs)
  where
      sq x = x ^ pow
      pow = 2
sumSquares [] = 0
 