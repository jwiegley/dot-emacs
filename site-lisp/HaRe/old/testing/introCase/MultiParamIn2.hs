module MultiParamIn2 where


f :: Maybe Int -> [Int] -> Int
f Nothing y  = hd y + hd (tl y)
f (Just x) y = x + hd y


hd y = head y
tl y = tail y