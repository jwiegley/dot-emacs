module B1 where

import Control.Parallel.Strategies

-- test when already import strategies the import doesn't change.

qsort (x:xs) = lsort_2 ++ [x] ++ hsort_2
  where
    lsort = qsort (filter (<) x xs)
    hsort = qsort (filter (>=) x xs)    
    (lsort_2, hsort_2)
        =   runEval
                (do lsort_2 <- rpar lsort
                    hsort_2 <- rpar hsort
                    return (lsort_2, hsort_2))