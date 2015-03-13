
-- Refactoring: move myFringe to module D1. This refactoring test the adding of import
-- declaration (see module A5) and also the change of qualifiers.

module C5(myFringe, Tree(..), SameOrNot(..))  where 

data Tree a = Leaf a | Branch (Tree a) (Tree a) 

sumTree:: (Num a) => Tree a -> a
sumTree (Leaf x ) = x
sumTree (Branch left right) = sumTree left + sumTree right

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left 

class SameOrNot a where
   isSame  :: a -> a -> Bool
   isNotSame :: a -> a -> Bool

instance SameOrNot Int where
   isSame a  b = a == b
   isNotSame a b = a /= b



