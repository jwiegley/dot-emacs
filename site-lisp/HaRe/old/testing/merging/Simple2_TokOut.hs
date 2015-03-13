module Simple2 where


f3 :: Num t  =>  t  ->  t  ->  (t, t)
f3 x y = (x + y, y - x)

-- f1 :: Int -> Int -> Int
f1 x y = x + y

f2 x y = y - x