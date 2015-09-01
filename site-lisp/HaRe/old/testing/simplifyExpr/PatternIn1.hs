module PatternIn1 where


f x = let g = 42 in case g of
                     42 -> 9
                     _ -> x



