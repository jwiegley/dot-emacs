module WhereIn3 where


f y = g y
     where
       g x@(Left a) = case x of
                        (Right b) -> b
                        (Left a)  -> a

