module Recursive9 where

f1 :: Int -> [a] -> [a]
f1 _ [] = []
f1 0 xs = (x:ls)
            where
              ls = f1 (n - 1) xs

f2 :: Int -> [a] -> [a]
f2 _ [] = []
f2 0 xs = xs
f2 n (x:xs) = rs
               where
                rs = f2 (n - 1) xs

