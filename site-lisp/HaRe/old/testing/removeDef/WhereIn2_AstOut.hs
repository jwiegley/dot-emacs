module WhereIn2 where
fac :: Int -> Int
 
fac 0 = 1
fac 1 = 1
fac n = n * (fac (n - 1))
 