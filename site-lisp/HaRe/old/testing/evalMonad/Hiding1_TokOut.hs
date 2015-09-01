module Hiding1 where

import Control.Parallel.Strategies hiding (rpar, runEval)

fib n 
  | n <= 1    = 1
  | otherwise = n1 + n2 + 1
      where
       n1 = fib (n-1)
       n2 = fib (n-2)


n1_2 = "bob"

