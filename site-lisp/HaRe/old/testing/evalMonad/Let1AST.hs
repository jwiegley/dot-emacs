module Let1 where
import Control.Parallel.Strategies (rpar, runEval)
fib n
    | n <= 1 = 1
    | otherwise =
        let n1 = fib (n - 1)
             
            n2 = fib (n - 2)
             
            n1_2
                =
                    runEval
                        (do n1_2 <- rpar n1
                            return n1_2)
        in (n1_2 + n2) + 1
 