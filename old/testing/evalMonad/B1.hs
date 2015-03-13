module B1 where

import Control.Parallel.Strategies

-- test when already import strategies the import doesn't change.

qsort (x:xs) = lsort ++ [x] ++ hsort
  where
    lsort = qsort (filter (<) x xs)
    hsort = qsort (filter (>=) x xs)