module MultiParamIn5 where
fromMaybe :: (Maybe a) -> a
 
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"
 
f :: (Maybe Int) -> [Int] -> (Either Int b) -> Int
 
f Nothing y@[] (Left a) = (hd y) + a
f Nothing y@(b_1 : b_2) (Left a) = (hd y) + a
f (Just b_1) y@[] (Right b_2)
    = (b_3 + (hd y)) + (fromMaybe b_1) where b_3 = 42
f (Just b_1) y@(b_5 : b_4) (Right b_2)
    = (b_3 + (hd y)) + (fromMaybe b_1) where b_3 = 42
f Nothing y (Left a) = (hd y) + a
f (Just b_1) y (Right b_2)
    = (b_3 + (hd y)) + (fromMaybe b_1) where b_3 = 42
 
hd x = head x
 
tl x = tail x
 