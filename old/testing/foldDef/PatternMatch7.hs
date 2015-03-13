module PatternMatch7 where


g = (\(y:ys) -> (case y of
                 p | p == 45 -> 12
                 _ -> 52))



f x = (\(p:ps) -> (case p of
             l | x == 45 -> 12
             _ -> 52))

