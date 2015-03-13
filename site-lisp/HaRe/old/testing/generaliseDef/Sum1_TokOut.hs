module Sum1 where

-- highlight 0, select GeneraliseDef "n"

import Prelude hiding (sum)

sum n []    = n 
sum n (h:t) = (+) h ((sum n) t)

main = sum 0 [1..4]
