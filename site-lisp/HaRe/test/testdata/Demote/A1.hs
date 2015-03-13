module Demote.A1 where

import Demote.C1 

main xs = case xs of 
             [] -> 0
             [x:xs] -> x^pow + sumSquares xs

