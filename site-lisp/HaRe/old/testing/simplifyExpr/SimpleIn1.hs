module SimpleIn1 where



f x@[] = case x of
            []     -> error "head:empty list"
            (x:xs) -> x

g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

