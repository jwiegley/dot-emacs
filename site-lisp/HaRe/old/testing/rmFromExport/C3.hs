
-- In this example, remove 'Tree(Leaf,Branch)' from the export. Note that this
-- refactoring does not handle sub entries in the export list and this may be
-- improved in the future.

module C3(sumTree, myFringe, Tree(Leaf,Branch), SameOrNot(..))  where 

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



