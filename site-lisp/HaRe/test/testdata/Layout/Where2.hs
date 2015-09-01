module Layout.Where2 where

tup@(h,t) = head $ zip [1..10] [3..ff]
  where
    ff :: Int
    ff = 15

x = 3
