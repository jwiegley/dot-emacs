module Guards1 where

f x
  | x == 1    = g (x + 1)
  | otherwise = g x
     where
       g x = 90 - x

