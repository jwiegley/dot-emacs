module B3 where
import Control.Parallel.Strategies (rseq, rpar,
                                    runEval)
qsort ((x : xs))
    = lsort ++ ([x] ++ hsort_2)
  where
      lsort = qsort (filter (<) x xs)
      hsort = qsort (filter (>=) x xs)
      hsort_2
          =
              runEval
                  (do hsort_2 <- rpar hsort
                      return hsort_2)
 