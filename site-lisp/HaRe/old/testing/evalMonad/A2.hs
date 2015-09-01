module A2 where

fib 1 = 1
fib n = n1 + n2 + 1
 where
   n1 = fib (n-1)
   n2 = fib (n-2)