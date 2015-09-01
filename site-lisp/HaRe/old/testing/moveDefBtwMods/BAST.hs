module B (myFringe) where
import D hiding (sumSquares, fringe)
import D (fringe)
import C hiding ()
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 