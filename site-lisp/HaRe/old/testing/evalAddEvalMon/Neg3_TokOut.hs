module Neg3 where

import Control.Parallel.Strategies

f  = 42

b = f 76

(g, b_2)
    =   runEval $
            (do d <- f
                b_2 <- rpar b
                return (d, b_2)) 