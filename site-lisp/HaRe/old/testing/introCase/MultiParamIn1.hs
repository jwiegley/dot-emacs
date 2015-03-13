module MultiParamIn1 where


f :: Maybe Int -> [Int] -> Int
f (Just x) y = x + hd y


hd y = head y