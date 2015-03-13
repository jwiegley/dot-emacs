module ListIn1 where
f :: [Int] -> Int
 
f [1, 2]
    =   case [1, 2] of
            [x, y] -> y
            _ -> 1
 
f_1 [1, 2]
    =   case [1, 2] of
            [x, y] -> return 0
            _ -> return 1
 