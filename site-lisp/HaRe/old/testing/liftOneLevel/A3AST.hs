module A3 where
import C3 (anotherFun)
import D3 (sumSquares)
main = (sumSquares [1 .. 4]) + (anotherFun [1 .. 4])
 