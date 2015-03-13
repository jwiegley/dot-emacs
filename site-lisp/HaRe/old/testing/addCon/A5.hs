module A5 where

data T a = T1 a  

data S = C1 | C2 | C3

over :: S -> (T Int) -> Int
over C1 x = 42
over C2 x = 43
over C3 x = 43