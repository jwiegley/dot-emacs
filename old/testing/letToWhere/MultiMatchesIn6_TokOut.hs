module MultiMatchesIn6 where

square x y = (sq x) + (sq y)
    where
      sq x 0 = 0
      sq x = x ^ pow
    

pow = 2

g = let blah = 42 + blah2
        blah2 = 9
     in blah
   