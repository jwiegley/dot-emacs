module Do1 where



fib n
 | n <=1 = return 1
 | otherwise 
     = do 
          n1 <- fib (n-1)
          n2 <- fib (n-2)
          return (n1 + n2 + 1)