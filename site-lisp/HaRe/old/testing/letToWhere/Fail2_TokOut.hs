module Fail2 where

f = let g xs = map (+1) xs in g list
      where
       list = [1,1,2,3,4]

    
