module C1 (module D1, module C1) where 

import D1 hiding (main, sq)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
    where sq x = x ^pow 
sumSquares1 [] = 0



