module Recursive2 where

-- source functions
f1 :: Int -> [a] -> [a]
f1 _ [] = []
f1 0 xs = []
f1 n (x:xs) = x : (f1 (n-1) xs)

f2 :: Int -> [a] -> [a]
f2 _ [] = []
f2 0 xs = xs
f2 n (x:xs) = f2 (n-1) xs

f3 :: Int -> Int
f3 42 = 56