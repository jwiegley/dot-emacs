module PatternMatch6 where


g = (\(y:ys) -> (case y of
                 p | p == 45 -> 12
                 _ -> 52))



f x = (\(p:ps) -> (case p of
             x | x == 45 -> 12
             _ -> 52))

