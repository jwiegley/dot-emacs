module List1 where


data T a = T1 a | T2 


f :: [T b] -> a -> Int
f [x, T1 o] g = 56
f [x, T2] g = 56 + 1

