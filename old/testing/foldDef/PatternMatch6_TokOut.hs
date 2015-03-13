module PatternMatch6 where


g = f undefined



f x = (\(p:ps) -> (case p of
             x | x == 45 -> 12
             _ -> 52))

