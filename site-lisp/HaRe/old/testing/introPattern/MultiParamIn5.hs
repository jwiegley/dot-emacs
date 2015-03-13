module MultiParamIn5 where

-- test checks for renaming conflicts
-- select y on LHS of f

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"


f :: Maybe Int -> [Int] -> Either Int b -> Int
f Nothing  y (Left a) = hd y + a
f (Just b_1) y (Right b_2) = b_3 + hd y + fromMaybe b_1
                              where b_3 = 42


hd x = head x
tl x = tail x


