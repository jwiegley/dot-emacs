module A4 where

-- here we have a top-level closure, computing something expensive...


import Control.Parallel.Strategies (rpar, runEval)

fib n
 | n <= 1 = 1
 | otherwise = fib (n-1) + fib (n-2)



bigFib = fib 200

evenBiggerFib = fib 30000


someComp = bigFib_2 + evenBiggerFib_2 + 42

closureY = bigFib_2 + 32
(bigFib_2, evenBiggerFib_2)
    =
        runEval
            (do bigFib_2 <- rpar bigFib
                evenBiggerFib_2 <- rpar evenBiggerFib
                return (bigFib_2, evenBiggerFib_2))
