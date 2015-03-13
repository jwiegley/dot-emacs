module B1 where

f = let g :: Int -> Int
         
        g x = sq x
    in let b = 43 in g b
       
       


sq x = x * x

