module SubSubPatternIn1 where



f :: [Int] -> Int
f (x : (y :ys)) = x + y