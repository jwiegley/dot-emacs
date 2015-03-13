module A1 where
import B1
import C1
import D1
main :: (AnotherTree Int) -> Bool
 
main t
    =   isSame (sumSquares (fringe t))
            ((sumSquares (B1.myFringe t)) +
                 (sumSquares (C1.myFringe t)))
 