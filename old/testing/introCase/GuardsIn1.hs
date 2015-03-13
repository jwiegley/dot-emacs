module GuardsIn1 where



f :: [Int] -> Int
f g 
   | g == [1]    = 42
   | otherwise = head g