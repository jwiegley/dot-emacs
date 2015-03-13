module ListIn3 where
f :: [Int] -> Int
 
f [42, 56]
    =   case [1] of
            [x, y] -> x
            _ -> 1
 
f_1 [42, 56]
    =   case [1] of
            [x, y] -> return 0
            _ -> return 1
 