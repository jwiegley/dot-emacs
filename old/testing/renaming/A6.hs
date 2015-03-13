module A6 where

import B6 
import C6 
import D6

main :: Tree Int ->Bool
main t = isSame (sumSquares (D6.myFringe t))
               (sumSquares (B6.myFringe t)+sumSquares (C6.myFringe t))

