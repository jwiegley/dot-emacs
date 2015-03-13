module A3 where

f = n1 + n2 + 1
 where
   n1 = fib 23
   n2 = fib 24

   fib n | n <= 1    = 1
         | otherwise =  fib (n-1) + fib (n-2) + 1