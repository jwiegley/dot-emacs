module D5 where
data Tree a = Leaf a | Branch (Tree a) (Tree a)
 
fringe :: (Tree a) -> [a]
 
fringe (Leaf x) = [x]
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
 
class SameOrNot a
  where
      isSame :: a -> a -> Bool
      isNotSame :: a -> a -> Bool
 
instance SameOrNot Int
  where
      isSame a b = a == b
      isNotSame a b = a /= b
 
sum ((x : xs))
    = (sq x) + (D5.sum xs)
  where
      sq x = x ^ pow
      pow = 2
sum [] = 0
 