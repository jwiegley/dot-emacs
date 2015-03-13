module LiftOneLevel.A3 where
 
import LiftOneLevel.C3 (anotherFun)
import LiftOneLevel.D3 (sumSquares)

main = sumSquares [1..4] + anotherFun [1..4] 
