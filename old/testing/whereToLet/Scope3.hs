module Scope3 where

f = let square x =  x + x in g 55
        where
          g x = square x 
          square x = x * x

          