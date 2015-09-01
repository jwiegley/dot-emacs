module ListIn2 where
f :: [Int] -> Int
 
f [42, 56]
    =   case [11, 2] of
            [x, y] -> x
            _ -> 1
 
f_1 [42, 56]
    =   case [11, 2] of
            [x, y] -> return 0
            _ -> return 1
 