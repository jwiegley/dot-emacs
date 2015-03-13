module A4 where
import D4
import C4
import B4
myFringe :: (Tree a) -> [a]
 
myFringe (Leaf x) = [x]
myFringe (Branch left right) = A4.myFringe right
 
main :: (Tree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
	    ((sumSquares (A4.myFringe t)) +
		 (sumSquares (C4.myFringe t)))
 