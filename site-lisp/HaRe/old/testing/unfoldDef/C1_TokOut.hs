module C1 where 

--Unfold 'sq'

import D1 hiding (main)

sumSquares1 (x:xs) = (x ^ pow) + sumSquares1 xs
 
sumSquares1 [] = 0

