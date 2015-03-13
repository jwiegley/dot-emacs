module Sum2 where

-- highlight (+), select GeneraliseDef "c"

import Prelude hiding (sum)

sum n []    = n 
sum n (h:t) = (+) h (sum n t)

main = sum 0 [1..4]
