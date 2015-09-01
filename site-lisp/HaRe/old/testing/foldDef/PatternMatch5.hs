module PatternMatch5 where


g x = (\(y:ys) -> (case y of
                 p -> 12
                 _ -> 52))



f x = (\(p:ps) -> (case p of
             x -> 12
             _ -> 52))

