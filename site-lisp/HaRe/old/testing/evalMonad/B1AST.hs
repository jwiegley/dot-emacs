module B1 where
import Control.Parallel.Strategies
qsort ((x : xs))
    = lsort_2 ++ ([x] ++ hsort)
  where
      lsort = qsort (filter (<) x xs)
      hsort = qsort (filter (>=) x xs)
      lsort_2
          =
              runEval
                  (do lsort_2 <- rpar lsort
                      return lsort_2)
 