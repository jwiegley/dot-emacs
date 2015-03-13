module Renaming.D1 where

{-Rename data constructor `Tree` to `AnotherTree`.
  This refactoring affects module `D1', 'B1' and 'C1' -}
   
data Tree a = Leaf a | Branch (Tree a) (Tree a) 

fringe :: Tree a -> [a]
fringe (Leaf x ) = [x]
fringe (Branch left right) = fringe left ++ fringe right

class SameOrNot a where
   isSame  :: a -> a -> Bool
   isNotSame :: a -> a -> Bool

instance SameOrNot Int where
   isSame a  b = a == b
   isNotSame a b = a /= b

sumSquares (x:xs) = sq x + sumSquares xs
    where sq x = x ^pow 
          pow = 2

sumSquares [] = 0
