module Record3 where

data C = F {f1, f2 :: Int, f3 :: Bool    }

f :: C -> Int
f (F {}) = 42

g = f1 (F 1 2 True)