module A5 where

import B5 
import C5 
import D5

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (B5.myFringe t)+sumSquares (C5.myFringe t))

