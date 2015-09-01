module MultiParamIn3 where


f :: Maybe Int -> [Int] -> Either Int b -> Int
f Nothing y  (Right b) = hd y + hd (tl y)
f (Just x) y (Left a) = x + hd y + a


hd y = head y
tl y = tail y