module Pat1 where

data T1 a b = C1 a b | C2 b a

res = x
       where
         (C1 x y) = (C1 1 2) 