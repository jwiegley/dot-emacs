module A7 where

import B7 
import C7

main :: Tree Int ->Int
main t = sumSquares (C7.myFringe t)+sumSquares (B7.myFringe t)

