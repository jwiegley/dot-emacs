module LambdaIn1 where
f z =   \ y@((j : js)) ->
            case y of
                [] -> error "Error: empty list!"
                (x : xs) -> x
 
f_1 z
    =   \ y@((j : js)) ->
            case y of
                [] -> return 0
                (x : xs) -> return 1
 