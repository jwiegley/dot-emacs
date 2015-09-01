
-- Refactoring: move myFringe to module D3. This example aims to test the change of qualifiers,
-- and the import/exports.
module C3(Tree(..), SameOrNot(..))  where 

data Tree a = Leaf a | Branch (Tree a) (Tree a) 

sumTree:: (Num a) => Tree a -> a
sumTree (Leaf x ) = x
sumTree (Branch left right) = sumTree left + sumTree right



class SameOrNot a where
   isSame  :: a -> a -> Bool
   isNotSame :: a -> a -> Bool

instance SameOrNot Int where
   isSame a  b = a == b
   isNotSame a b = a /= b

