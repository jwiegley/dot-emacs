module D3 (myFringe, fringe, sumSquares) where
import C3
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = myFringe left
 
fringe :: (Tree a) -> [a]
 
fringe (Leaf x) = [x]
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
 
sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
sumSquares [] = 0
 
sq x = x ^ pow
 
pow = 2
 