module A3 where
import D3
import C3
import B3
main :: (Tree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
	    ((sumSquares (B3.myFringe t)) +
		 (sumSquares (D3.myFringe t)))
 