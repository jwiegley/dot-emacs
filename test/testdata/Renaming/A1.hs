module Renaming.A1 where

import Renaming.B1
import Renaming.C1
import Renaming.D1

main :: Tree Int ->Bool
main t = isSame (sumSquares (fringe t))
               (sumSquares (Renaming.B1.myFringe t)+sumSquares (Renaming.C1.myFringe t))

