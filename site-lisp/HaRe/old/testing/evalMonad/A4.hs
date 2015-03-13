module A4 where

-- here we have a top-level closure, computing something expensive...


fib n
 | n <= 1 = 1
 | otherwise = fib (n-1) + fib (n-2)



bigFib = fib 200

evenBiggerFib = fib 30000


someComp = bigFib + evenBiggerFib + 42

closureY = bigFib + 32

