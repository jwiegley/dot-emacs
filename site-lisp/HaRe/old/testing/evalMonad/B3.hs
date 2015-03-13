module B3 where

import Control.Parallel.Strategies (rseq, rpar)

-- test when already import strategies the import doesn't change.

-- here we need to add rpar and runEval to the import list

qsort (x:xs) = lsort ++ [x] ++ hsort
  where
    lsort = qsort (filter (<) x xs)
    hsort = qsort (filter (>=) x xs)
