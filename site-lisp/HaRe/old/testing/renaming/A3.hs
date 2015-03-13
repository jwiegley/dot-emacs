module A3 where

import B3 
import C3 
import D3

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (B3.myFringe t)+sumSquares (C3.myFringe t))

