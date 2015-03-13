module MultiParamIn1 where


f :: Maybe Int -> [Int] -> Int
f (Just x) y
    =   case y of
            y@[] -> x + (hd y)
            y@(b_1 : b_2) -> x + (hd y)
f (Just x) y = x + (hd y)


hd y = head y