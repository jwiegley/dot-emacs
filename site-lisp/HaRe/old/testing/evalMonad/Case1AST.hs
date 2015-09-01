module Case1 where
import Control.Parallel.Strategies (rpar, runEval)
fib n
    | n <= 1 = 1
    | otherwise =
        case (fib (n - 1), fib (n - 2)) of
            (n1, n2)
                -> (n1_2 + n2) + 1
              where
                  n1_2
                      =
                          runEval
                              (do n1_2 <- rpar n1
                                  return n1_2)
 