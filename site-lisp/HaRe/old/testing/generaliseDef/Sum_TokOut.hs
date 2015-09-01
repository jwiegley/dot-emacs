module Sum where

--highlight (+), select GeneraliseDef "c"

import Prelude hiding (sum)

fun1 = x + x 

sum c []    = 0 
sum c (h:t) = c h (sum c t)

main = sum (+) [1..4]
