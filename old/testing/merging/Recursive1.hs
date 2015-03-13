module Recursive1 where

-- source functions
f1 :: Int -> [a] -> [a]
f1 _ [] = []
f1 0 xs = []
f1 n (x:xs) = x : (f1 (n-1) xs)

f2 :: Int -> [a] -> [a]
f2 _ [] = []
f2 0 xs = xs
f2 n (x:xs) = f2 (n-1) xs

-- this is what the fused function should ideally look like
f3 :: Int -> [a] -> ([a], [a])
f3 _ [] = ([], [])
f3 0 xs = ([], xs)
f3 n (x:xs) = (x : (fst (f3 (n-1) xs)), (snd (f3 (n-1) xs)))