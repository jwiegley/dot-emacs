module LiftToToplevel.A3 where
 
import LiftToToplevel.C3 (anotherFun)
import LiftToToplevel.D3 (sumSquares) 

main  = sumSquares [1..4] + anotherFun [1..4] 

