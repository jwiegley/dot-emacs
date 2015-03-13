module PatternMatch1 where


g = (\y -> f y)



f x = case x of
        (x:s) -> 12
        _ -> 52

