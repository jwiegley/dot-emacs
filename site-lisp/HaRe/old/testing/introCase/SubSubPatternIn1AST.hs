module SubSubPatternIn1 where
f :: [Int] -> Int
 
f ((x : (y : ys)))
    =   case ys of
            ys@[] -> x + y
            ys@(b_1 : b_2) -> x + y
f ((x : (y : ys))) = x + y
 