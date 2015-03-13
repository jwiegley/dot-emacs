module Renaming.A2 where

import Renaming.B2 
import Renaming.C2 
import Renaming.D2

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B2.myFringe t)+sumSquares (Renaming.C2.myFringe t))

