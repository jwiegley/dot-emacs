module DeepSeq2 where

import qualified Control.Parallel.Strategies as CP

fib t n 
  | n <= 1    = 1
  | otherwise = n1_2 + n2_2 + 1
      where
       n1 = fib 20 (n-1)
       n2 = fib 20 (n-2)
       (n1_2, n2_2)
           =   CP.runEval
                   (do n1_2 <- (rpar_abs_1 `CP.dot` CP.rdeepseq) n1
                       n2_2 <- (rpar_abs_1 `CP.dot` CP.rdeepseq) n2
                       return (n1_2, n2_2))
         where
             rpar_abs_1
                 | n > t = CP.rpar
                 | otherwise = CP.rseq


n1_2 = fib 20 42

