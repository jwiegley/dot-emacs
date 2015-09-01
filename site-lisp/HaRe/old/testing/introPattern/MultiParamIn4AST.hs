module MultiParamIn4 where
fromMaybe :: (Maybe a) -> a
 
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"
 
f :: (Maybe Int) -> [Int] -> (Either Int b) -> Int
 
f Nothing y@[] (Left a) = (hd y) + a
f Nothing y@(b_1 : b_2) (Left a) = (hd y) + a
f (Just b_1) y@[] (Right b_2)
    = (hd y) + (fromMaybe b_1)
f (Just b_1) y@(b_4 : b_3) (Right b_2)
    = (hd y) + (fromMaybe b_1)
f Nothing y (Left a) = (hd y) + a
f (Just b_1) y (Right b_2) = (hd y) + (fromMaybe b_1)
 
hd x = head x
 
tl x = tail x
 