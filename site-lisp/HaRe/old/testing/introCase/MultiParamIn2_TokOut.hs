module MultiParamIn2 where


f :: Maybe Int -> [Int] -> Int
f Nothing y
    =   case y of
            y@[] -> (hd y) + (hd (tl y))
            y@(b_1 : b_2) -> (hd y) + (hd (tl y))
f (Just x) y
    =   case y of
            y@[] -> x + (hd y)
            y@(b_1 : b_2) -> x + (hd y)
f Nothing y = (hd y) + (hd (tl y))
f (Just x) y = x + (hd y)


hd y = head y
tl y = tail y