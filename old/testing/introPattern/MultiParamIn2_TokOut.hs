module MultiParamIn2 where

-- select x on lhs of f; should introduce product of patterns
-- for f

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"


f :: Maybe Int -> [Int] -> Int
f Nothing y@[] = hd y
f Nothing y@(b_1 : b_2) = hd y
f (Just x) y@[] = (hd y) + (fromMaybe x)
f (Just x) y@(b_1 : b_2) = (hd y) + (fromMaybe x)
f Nothing y = hd y
f (Just x) y = (hd y) + (fromMaybe x)


hd x = head x
tl x = tail x


