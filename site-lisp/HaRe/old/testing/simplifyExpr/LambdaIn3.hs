module LambdaIn3 where


f = (\g@(x:xs) -> case g of
                   [] -> error "Error!"
                   (l:ls) -> l) [1,2]



