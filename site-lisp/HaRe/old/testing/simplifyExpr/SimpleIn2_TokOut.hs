module SimpleIn2 where



f x@(y:ys) = y


g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

