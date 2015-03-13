module Record1 where

data C = F {f44 :: String, f1, f2 :: Int, f3 :: Bool}

g = f1 (F undefined 1 2 True)