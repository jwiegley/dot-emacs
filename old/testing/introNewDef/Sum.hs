module Sum where

--highlight "fold (+) 0", select IntroNewDef "sum"

import Prelude hiding (sum)

fold c n []    = n 
fold c n (h:t) = c h (fold c n t)

main = fold (+) 0 [1..4]
