module MultiParamIn3 where

-- select x on lhs of f; should introduce product of patterns
-- for f

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"


f :: Maybe Int -> [Int] -> Either Int b -> Int
f Nothing  y (Left a) = hd y + a
f (Just x) y (Right b) = hd y + fromMaybe x


hd x = head x
tl x = tail x


