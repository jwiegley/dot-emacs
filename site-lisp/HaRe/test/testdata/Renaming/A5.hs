module Renaming.A5 where

import Renaming.B5 
import Renaming.C5 
import Renaming.D5

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B5.myFringe t)+sumSquares (Renaming.C5.myFringe t))

