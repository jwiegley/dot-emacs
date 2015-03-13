module A1 where
g n l = (take n l, drop n l)
 
f1 :: Int -> String -> String
 
f1 n l = take n l
 
f2 :: Int -> String -> String
 
f2 n l = drop n l
 