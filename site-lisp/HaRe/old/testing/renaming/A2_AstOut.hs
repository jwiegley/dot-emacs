module A2 where
import B2
import C2
import D2
main :: (Tree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
	    ((sumSquares (B2.myFringe t)) +
		 (sumSquares (C2.myFringe t)))
 