module A5 where

import B5 
import C5

main :: Tree Int ->Int
main t = sumSquares (C5.myFringe t)+sumSquares (B5.myFringe t)

