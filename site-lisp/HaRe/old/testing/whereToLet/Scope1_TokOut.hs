module Scope1 where



f x = let square x =  x + x in g x
        where
          g x = square x 
          square x = x * x

          