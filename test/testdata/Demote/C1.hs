module Demote.C1 (module Demote.D1, module Demote.C1) where 

import Demote.D1 hiding (main, sq)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
    where sq x = x ^pow 
sumSquares1 [] = 0



