module Monad2 where

f x y = do
       return ((sq x) * (sq y))    
    where
      pow = 2
      sq 0 = 0
      sq x = x ^ pow
    

