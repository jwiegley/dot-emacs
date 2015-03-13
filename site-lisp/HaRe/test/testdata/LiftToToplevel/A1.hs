module LiftToToplevel.A1 where
 
import LiftToToplevel.C1 

main xs = case xs of 
             [] -> 0
             [x:xs] -> x^pow + sumSquares1 xs

