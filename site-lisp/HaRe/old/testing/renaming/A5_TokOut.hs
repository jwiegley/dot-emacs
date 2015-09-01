module A5 where

import B5 
import C5 
import D5

main :: Tree Int ->Bool
main t = isSame (D5.sum (fringe t))
               (D5.sum (B5.myFringe t)+D5.sum (C5.myFringe t))

