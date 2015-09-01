module SimpleIn1 where
f x@[]
    =   case x of
            [] -> error "head:empty list"
            (x : xs) -> x
 
f_1 x@[]
    =   case x of
            [] -> return 0
            (x : xs) -> return 1
 
g :: [Int] -> Int
 
g ((x : xs)) = x + (head (tail xs))
 