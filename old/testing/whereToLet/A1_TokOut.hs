module A1 where

f x = let g :: Int -> Int
           
          g x = sq x
      in let b = 43 in g b
       
       


sq x = x * x

