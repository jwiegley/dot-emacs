module GuardsIn1 where



f :: [Int] -> Int
f g =   case g of
            g@[]
                | g == [1] -> 42
                | otherwise -> head g
            g@(b_1 : b_2)
                | g == [1] -> 42
                | otherwise -> head g
f g | g == [1] = 42
    | otherwise = head g