module Recursive1 where


g :: (Eq a1, Num a1)  =>  a1  ->  [a]  ->  ([a], [a])
g _ [] = ([], [])
g 0 xs = ([], xs)
g n ((x : xs))
    = (x : (fst $ g (n - 1) xs), snd $ g (n - 1) xs)

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