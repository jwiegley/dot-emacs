module PatternMatch2 where


g = (\y -> case y of
                 p -> 12
                 _ -> 52)



f x = case x of
        (x:s) -> 12
        _ -> 52

