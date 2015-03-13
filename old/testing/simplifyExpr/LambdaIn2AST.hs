module LambdaIn2 where
f   =   \ g@((z : zs)) ->
            \ ((i : is)) ->
                case g of
                    [] -> error "Error!"
                    (x : xs) -> x : [i]
 
f_1 =   \ g@((z : zs)) ->
            \ ((i : is)) ->
                case g of
                    [] -> return 0
                    (x : xs) -> return 1
 