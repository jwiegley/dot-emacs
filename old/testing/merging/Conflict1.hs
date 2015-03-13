module Conflict1 where

f :: Int -> Int
f x = x + 1


f1 :: Int -> Int
f1 x = x - 1

f3 :: Int -> (Int, Int)
f3 x y = (x + 1, y - 1) 