module EqualsIn1 where
f :: [Int] -> Bool
 
f x@[]
    =   case (x, []) of
            ([], []) -> True
            ((x : xs), (y : ys)) -> (x == y) && (xs == ys)
            (_, _) -> False
f x@((b_1 : b_2))
    =   case (x, []) of
            ([], []) -> True
            ((x : xs), (y : ys)) -> (x == y) && (xs == ys)
            (_, _) -> False
f x =   case (x, []) of
            ([], []) -> True
            ((x : xs), (y : ys)) -> (x == y) && (xs == ys)
            (_, _) -> False
 
f_1 x@[]
    =   case (x, []) of
            ([], []) -> return 0
            ((x : xs), (y : ys)) -> return 1
            (_, _) -> return 2
 