module New where

f :: [Int] -> Int
f x@[] = (head x) + (head (tail x))
f x@(b_1 : b_2) = (b_1) + (head (tail x))
f x = (head x) + (head (tail x))


