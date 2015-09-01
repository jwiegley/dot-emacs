module LambdaIn3 where
f   =   (\ g@((x : xs)) ->
             case g of
                 [] -> error "Error!"
                 (l : ls) -> l)
            [1, 2]
 
f_1 =   (\ g@((x : xs)) ->
             case g of
                 [] -> return 0
                 (l : ls) -> return 1)
            [1, 2]
 