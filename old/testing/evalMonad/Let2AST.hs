module Let2 where
import Control.Parallel.Strategies (rpar, runEval)
fib n
    | n <= 1 = 1
    | otherwise =
        let n1
                = fib n'_2
              where
                  n' = n - 1
                  n'_2
                      =
                          runEval
                              (do n'_2 <- rpar n'
                                  return n'_2)
             
            n2 = fib (n - 2)
        in (n1 + n2) + 1
 