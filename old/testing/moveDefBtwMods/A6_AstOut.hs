module A6 where
import B6
import C6
import D6 (myFringe)
main :: (Tree Int) -> Int
 
main t
    =   (sumSquares (D6.myFringe t)) +
	    (sumSquares (B6.myFringe t))
 