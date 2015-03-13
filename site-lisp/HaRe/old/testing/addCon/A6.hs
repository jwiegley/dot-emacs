module A6 where

data T a = T1 a | T2 a

data S = C1 | C2 | C3

over :: S -> (T Int) -> Int
over x (T1 y) = 42
over x (T2 y) = 42