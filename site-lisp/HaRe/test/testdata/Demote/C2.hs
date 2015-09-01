module Demote.C2 (module Demote.D2, module Demote.C2) where 

import Demote.D2 hiding (main, sq)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
    where sq x = x ^pow 
sumSquares1 [] = 0



