module Let1 where
f3 x
    =   let ls = x + 1
             
            rs = x - 1
        in (ls, rs)
 
f1 :: Int -> Int
 
f1 x = let ls = x + 1 in ls
 
f2 :: Int -> Int
 
f2 x = let rs = x - 1 in rs
 