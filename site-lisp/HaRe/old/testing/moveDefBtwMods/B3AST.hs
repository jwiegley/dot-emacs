module B3 (myFringe) where
import D3 hiding (myFringe, sumSquares, fringe)
import D3 (fringe)
import C3 hiding ()
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 