module PatBindIn1 where
main :: Int
 
main = foo 3
 
foo :: Int -> Int
 
foo x = (h_1 + t) + (snd tup_1)
 
tup_1 :: (Int, Int)
 
tup_1@(h_1, t) = head $ (zip [1 .. 10] [3 .. 15])
 
tup = 10
 
h = 17
 