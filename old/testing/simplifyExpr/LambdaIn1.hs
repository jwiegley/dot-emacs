module LambdaIn1 where



f z = \y@(j:js) -> case y of
                    []     -> error "Error: empty list!"
                    (x:xs) -> x


