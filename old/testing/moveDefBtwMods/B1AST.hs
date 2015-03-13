module B1 (myFringe) where
import D1 hiding (sumSquares)
import D1 ()
import C1 hiding (myFringe)
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 