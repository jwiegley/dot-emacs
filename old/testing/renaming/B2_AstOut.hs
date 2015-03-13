module B2 (myFringe) where
import D2 hiding (sumSquares)
import qualified D2
instance SameOrNot Float
  where
      isSame a b = a == b
      isNotSame a b = a /= b
 
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (SubTree left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 