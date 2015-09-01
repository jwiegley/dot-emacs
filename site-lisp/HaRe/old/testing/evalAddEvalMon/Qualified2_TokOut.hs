module Qualified2 where

-- import qualified Control.Parallel.Strategies as T

import qualified Control.Parallel.Strategies as S


-- should fail, as there are two possible qualifiers...

fib n 
  | n <= 1    = 1
  | otherwise = n1_2 + n2_2 + 1
      where
       n1 = fib (n-1)
       n2 = fib (n-2)
       (n1_2, n2_2)
           =   S.runEval
                   (do n1_2 <- S.rpar n1
                       n2_2 <- S.rpar n2
                       return (n1_2, n2_2))

n1_2 = "bob"

