module A1 where

import Control.Parallel.Strategies (rpar, runEval)

fib n 
  | n <= 1    = 1
  | otherwise = n1_2 + n2_2 + 1
      where
       n1 = fib (n-1)
       n2 = fib (n-2)
       (n1_2, n2_2)
          =
               runEval
                   (do n1_2 <- rpar n1
                       n2_2 <- rpar n2
                       return (n1_2, n2_2))




n1_2 = fib 42

