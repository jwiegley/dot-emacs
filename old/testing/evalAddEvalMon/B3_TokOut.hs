module B3 where

import Control.Parallel.Strategies (rpar, runEval, rseq)

-- test when already import strategies the import doesn't change.

-- here we need to add rpar and runEval to the import list

qsort (x:xs) = lsort_2 ++ [x] ++ hsort_2
  where
    lsort = qsort (filter (<) x xs)
    hsort = qsort (filter (>=) x xs)
    (hsort_2, lsort_2)
        =   runEval
                (do hsort_2 <- rpar hsort
                    lsort_2 <- rpar lsort
                    return (hsort_2, lsort_2))