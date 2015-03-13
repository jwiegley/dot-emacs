module D3 where

{-Rename class name 'SameOrNot' to 'Same'.
  This refactoring affects module `D3', 'B3' and 'C3' -}
   
data Tree a = Leaf a | Branch (Tree a) (Tree a) 

fringe :: Tree a -> [a]
fringe (Leaf x ) = [x]
fringe (Branch left right) = fringe left ++ fringe right

class Same a where
   isSame  :: a -> a -> Bool
   isNotSame :: a -> a -> Bool

instance Same Int where
   isSame a  b = a == b
   isNotSame a b = a /= b

sumSquares (x:xs) = sq x + sumSquares xs
    where sq x = x ^pow 
          pow = 2

sumSquares [] = 0
