module PatternIn2 where


f (z:zs) = let y = (z:zs) in case y of
                              [] -> error "Error: empty list!"
                              (x:xs) -> x



