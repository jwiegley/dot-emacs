module A2 where
 
import C2 

import D2

sumSq xs = sum (map sq xs) + sumSquares xs + sumSquares1 xs

sq_f_2  = 2

main = sumSq [1..4]

