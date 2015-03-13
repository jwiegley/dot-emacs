module PatternMatch3 where


g = (\(y:ys) -> f y)



f x = case x of
        x -> 12
        _ -> 52

