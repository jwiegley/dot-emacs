module LiftOneLevel.A1 where
 
import LiftOneLevel.C1

main xs = case xs of
             [] -> 0
             [x:xs] -> x^pow + sumSquares1 xs
