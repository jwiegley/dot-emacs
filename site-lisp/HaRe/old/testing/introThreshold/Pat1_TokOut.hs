module Pat1 where

import Control.Parallel.Strategies (rpar, runEval,rseq)

f t
  = n1_2 + n2_2 + 1
      where
       n1 = f 20
       n2 = f 20
       (n1_2, n2_2)
           =   runEval
                   (do n1_2 <- rpar_abs_1 n1
                       n2_2 <- rpar_abs_1 n2
                       return (n1_2, n2_2))
         where
             rpar_abs_1
                 | ((n1_2 + n2_2) + 1) > t = rpar
                 | otherwise = rseq




n1_2 = f 20
