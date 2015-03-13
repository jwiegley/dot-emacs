module Sum1 where

-- highlight 0, select GeneraliseDef "n"

import Prelude hiding (sum)

sum []    = 0 
sum (h:t) = (+) h (sum t)

main = sum [1..4]
