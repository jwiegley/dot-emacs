module B4 (myFringe) where
import D4 hiding (sumSquares)
import qualified D4
instance SameOrNot Float
  where
      isSameOrNot a b = a == b
      isNotSame a b = a /= b
 
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 