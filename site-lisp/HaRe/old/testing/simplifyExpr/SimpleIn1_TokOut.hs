module SimpleIn1 where



f x@[] = error "head:empty list"


g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

