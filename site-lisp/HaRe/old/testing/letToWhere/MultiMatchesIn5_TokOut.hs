module MultiMatchesIn5 where

square x y = (sq x) + (sq y)
    where
      pow = 2
      sq x 0 = 0
      sq x = x ^ pow
    

                

g = let blah = 42 + blah2
        blah2 = 9
     in blah
   