module A1 where

f x = let b = 43 in g b
       where
        g :: Int -> Int
        g x = sq x
       


sq x = x * x

