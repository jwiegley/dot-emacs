module PatternMatch3 where


g = (\(y:ys) -> case y of
                 p -> 12
                 _ -> 52)



f x = case x of
        x -> 12
        _ -> 52

