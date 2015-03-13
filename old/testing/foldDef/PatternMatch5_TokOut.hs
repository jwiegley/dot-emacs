module PatternMatch5 where


g x = f undefined



f x = (\(p:ps) -> (case p of
             x -> 12
             _ -> 52))

