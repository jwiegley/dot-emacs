module Renaming.A3 where

import Renaming.B3 
import Renaming.C3 
import Renaming.D3

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B3.myFringe t)+sumSquares (Renaming.C3.myFringe t))

