module B5 (myFringe, sumSquares) where
import D5 hiding (myFringe, sumSquares, fringe)
import D5 (fringe)
import C5 hiding ()
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe right
 
sumSquares ((x : xs)) = (x ^ 2) + (sumSquares xs)
sumSquares [] = 0
 