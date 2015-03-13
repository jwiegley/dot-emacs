module Case2 where




import Control.Parallel.Strategies (rpar, runEval)

fib n 
  | n <= 1 = 1
  | otherwise = case (fib (n-1), fib (n-2)) of
                  (n1, n2) -> n1_3 + n2_2 + 1
                     where n1_2 = "blah"
                           
                           (n1_3, n2_2)
                               =   runEval
                                       (do n1_3 <- rpar n1
                                           n2_2 <- rpar n2
                                           return (n1_3, n2_2))                  