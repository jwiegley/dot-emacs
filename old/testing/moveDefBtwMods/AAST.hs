module A where
import D
import C
import B
import A5 (myFringe)
main :: (Tree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
	    ((sumSquares (B.myFringe t)) +
		 (sumSquares (A5.myFringe t)))
 