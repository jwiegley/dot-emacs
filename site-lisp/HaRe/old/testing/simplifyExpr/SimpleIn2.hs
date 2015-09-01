module SimpleIn2 where



f x@(y:ys) = case x of
              []     -> error "head:empty list"
              (x:xs) -> x


g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

