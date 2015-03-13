module D4 where
data Tree a = Leaf a | Branch (Tree a) (Tree a)
 
fringe :: (Tree a) -> [a]
 
fringe (Leaf x) = [x]
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
 
class SameOrNot a
  where
      isSameOrNot :: a -> a -> Bool
      isNotSame :: a -> a -> Bool
 
instance SameOrNot Int
  where
      isSameOrNot a b = a == b
      isNotSame a b = a /= b
 
sumSquares ((x : xs))
    = (sq x) + (sumSquares xs)
  where
      sq x = x ^ pow
      pow = 2
sumSquares [] = 0
 