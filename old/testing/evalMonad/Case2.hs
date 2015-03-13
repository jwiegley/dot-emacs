module Case2 where




fib n 
  | n <= 1 = 1
  | otherwise = case (fib (n-1), fib (n-2)) of
                  (n1, n2) -> n1 + n2 + 1
                     where n1_2 = "blah"
                  