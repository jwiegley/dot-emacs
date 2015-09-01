module Qualified1 where

import qualified Control.Parallel.Strategies as CP 

fib n 
  | n <= 1    = 1
  | otherwise = n1_2 + n2_2 + 1
      where
       n1 = fib (n-1)
       n2 = fib (n-2)
       (n1_2, n2_2)
          =
               CP.runEval
                   (do n1_2 <- CP.rpar n1
                       n2_2 <- CP.rpar n2
                       return (n1_2, n2_2))




n1_2 = fib 42

