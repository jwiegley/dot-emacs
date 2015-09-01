module A where

import D
import C
import B 

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (B.myFringe t)+sumSquares (C.myFringe t))

