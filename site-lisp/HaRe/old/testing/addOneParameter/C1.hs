module C1 where 

import D1 

sumSquares1 (x:xs) = sq x + sumSquares1 xs
 
sumSquares1 [] = 0
  


