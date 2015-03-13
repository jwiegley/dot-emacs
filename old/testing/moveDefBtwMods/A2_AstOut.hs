module A2 where
import D2
import C2
import B2
main :: (Tree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
	    ((sumSquares (B2.myFringe t)) +
		 (sumSquares (C2.myFringe t)))
 