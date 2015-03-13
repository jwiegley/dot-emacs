module LambdaIn2 where



f = \g@(z:zs) -> \(i:is) -> case g of
                            [] -> error "Error!"
                            (x:xs) -> x : [i] 


