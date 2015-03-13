module Guards4In where



f x@(Left a) = case x of
                   (Left x)
                       | x == 1 -> Right x
                       | otherwise -> Left x
                   (Right b) -> Left b



