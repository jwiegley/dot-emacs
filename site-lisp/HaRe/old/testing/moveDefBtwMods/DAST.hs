module D (fringe, sumSquares) where
import C
fringe :: (Tree a) -> [a]
 
fringe (Leaf x) = [x]
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
 
sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
sumSquares [] = 0
 
sq x = x ^ pow
 
pow = 2
 