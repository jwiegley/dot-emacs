module Record1 where

data C = F {f1, f2 :: Int, f3 :: Bool    }

f (F {f1 = 12, f2 = 42, f3 = True}) = True

g = f1 (F 1 2 True)