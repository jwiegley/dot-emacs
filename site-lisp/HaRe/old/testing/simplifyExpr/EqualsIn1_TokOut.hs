module EqualsIn1 where


f :: [Int] -> Bool
f x@[]
    =   True
f x@(b_1 : b_2)
    =   case (x, []) of
            ([], []) -> True
            ((x : xs), (y : ys)) -> (x == y) && (xs == ys)
            (_, _) -> False
f x =   case (x, []) of
            ([], []) -> True
            ((x : xs), (y : ys)) -> (x == y) && (xs == ys)
            (_, _) -> False


