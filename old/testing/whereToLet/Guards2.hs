module Guards2 where

f x
  | x == 1    = g (x + 1)
  | otherwise = g x
     where
       g :: Int -> Int
       g 1 = 45
       g x = 90 - x

