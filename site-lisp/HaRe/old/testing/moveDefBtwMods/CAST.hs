module C (Tree(..), SameOrNot(..)) where
data Tree a = Leaf a | Branch (Tree a) (Tree a)
 
sumTree :: Num a => (Tree a) -> a
 
sumTree (Leaf x) = x
sumTree (Branch left right)
    = (sumTree left) + (sumTree right)
 
class SameOrNot a
  where
      isSame :: a -> a -> Bool
      isNotSame :: a -> a -> Bool
 
instance SameOrNot Int
  where
      isSame a b = a == b
      isNotSame a b = a /= b
 