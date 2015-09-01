module Sum where

--highlight (+), select GeneraliseDef "c"

import Prelude hiding (sum)

fun1 = x + x 

sum []    = 0 
sum (h:t) = (+) h (sum t)

main = sum [1..4]
