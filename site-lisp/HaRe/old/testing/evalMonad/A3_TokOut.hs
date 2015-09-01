module A3 where

import Control.Parallel.Strategies (rpar, runEval)

f = n1_2 + n2 + 1
 where
   n1 = fib 23
   n2 = fib 24

   fib n | n <= 1    = 1
         | otherwise =  fib (n-1) + fib (n-2) + 1   
   n1_2
       =
           runEval
               (do n1_2 <- rpar n1
                   return n1_2)
