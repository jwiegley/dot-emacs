module C3 (module C3, module D3) where 

import D3 hiding (main)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
 
sumSquares1 [] = 0

