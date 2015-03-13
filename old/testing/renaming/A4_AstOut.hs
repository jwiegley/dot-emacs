module A4 where
import B4
import C4
import D4
main :: (Tree Int) -> Bool
 
main t
    =   isSameOrNot (sumSquares (fringe t))
	    ((sumSquares (B4.myFringe t)) +
		 (sumSquares (C4.myFringe t)))
 