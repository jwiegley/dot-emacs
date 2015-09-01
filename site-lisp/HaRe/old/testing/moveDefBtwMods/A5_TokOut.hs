module A5 where

import B5 
import C5
import D5 (myFringe)

main :: Tree Int ->Int
main t = sumSquares (D5.myFringe t)+sumSquares (B5.myFringe t)

