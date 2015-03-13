module Monad4 where

f x y = do
       let sq 0 = 0
           sq x = x ^ pow
           pow  = 2

       return (sq x * sq y)    


