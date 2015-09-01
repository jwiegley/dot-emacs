module MultiParamIn3 where


f :: Maybe Int -> [Int] -> Either Int b -> Int
f Nothing y (Right b)
    =   case y of
            y@[] -> (hd y) + (hd (tl y))
            y@(b_1 : b_2) -> (hd y) + (hd (tl y))
f (Just x) y (Left a)
    =   case y of
            y@[] -> (x + (hd y)) + a
            y@(b_1 : b_2) -> (x + (hd y)) + a
f Nothing y (Right b) = (hd y) + (hd (tl y))
f (Just x) y (Left a) = (x + (hd y)) + a


hd y = head y
tl y = tail y