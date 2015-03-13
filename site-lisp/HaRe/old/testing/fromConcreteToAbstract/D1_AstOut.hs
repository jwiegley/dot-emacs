module D1 (fringe, sumSquares) where
import C1
fringe :: (Tree a) -> [a]
 
fringe p | isLeaf p = [(leaf1 p)]
fringe p
    | isBranch p =
	(fringe (branch1 p)) ++ (fringe (branch2 p))
 
sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
sumSquares [] = 0
 
sq x = x ^ pow
 
pow = 2
 