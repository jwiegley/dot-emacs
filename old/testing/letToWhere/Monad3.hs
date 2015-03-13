module Monad3 where

f x y = do
       let sq 0 = 0
           sq x = x ^ pow


       return (sq x * sq y)    
    where
      pow = 2
      sq x = x * x

