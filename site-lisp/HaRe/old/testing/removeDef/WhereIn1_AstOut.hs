module WhereIn1 where
fac,fib :: Int -> Int
 
fac 0 = 1
fac 1 = 1
fac n = n * (fac (n - 1))
 
fib 0 = 1
fib 1 = 1
fib n = (fib (n - 1)) + (fib (n - 2))
 