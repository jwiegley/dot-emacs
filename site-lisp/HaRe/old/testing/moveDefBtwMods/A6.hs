module A6 where

import B6 
import C6

main :: Tree Int ->Int
main t = sumSquares (C6.myFringe t)+sumSquares (B6.myFringe t)

