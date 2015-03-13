module A4 where

import D4
import C4
import B4 

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (B4.myFringe t)+sumSquares (C4.myFringe t))

