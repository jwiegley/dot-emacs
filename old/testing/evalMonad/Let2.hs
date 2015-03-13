module Let2 where



fib n | n <= 1    = 1
      | otherwise = let n1 = fib n'
                         where n' = n-1 
                        n2 = fib (n-2)
                    in n1 + n2 + 1