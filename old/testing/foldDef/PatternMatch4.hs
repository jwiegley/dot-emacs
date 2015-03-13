module PatternMatch4 where


g x = (\(y:ys) -> (case y of
                 p -> 12
                 _ -> 52))



f x = (\p -> (case p of
             x -> 12
             _ -> 52))

