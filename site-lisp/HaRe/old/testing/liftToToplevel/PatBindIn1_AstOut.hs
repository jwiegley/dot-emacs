module PatBindIn1 where
main :: Int
 
main = foo 3
 
foo :: Int -> Int
 
foo x = (h + t) + (snd tup)
 
tup :: (Int, Int)
 
tup@(h, t) = head $ (zip [1 .. 10] [3 .. 15])
 