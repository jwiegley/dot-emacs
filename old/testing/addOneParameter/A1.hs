module A1 where
 
import C1 

import D1

sumSq xs = sum (map sq xs) + sumSquares xs + sumSquares1 xs

main = sumSq [1..4]

