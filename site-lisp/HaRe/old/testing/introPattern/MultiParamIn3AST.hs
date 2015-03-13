module MultiParamIn3 where
fromMaybe :: (Maybe a) -> a
 
fromMaybe (Just x) = x
fromMaybe Nothing = error "fromMaybe: Nothing"
 
f :: (Maybe Int) -> [Int] -> (Either Int b) -> Int
 
f Nothing y@[] (Left a) = (hd y) + a
f Nothing y@(b_1 : b_2) (Left a) = (hd y) + a
f (Just x) y@[] (Right b) = (hd y) + (fromMaybe x)
f (Just x) y@(b_1 : b_2) (Right b)
    = (hd y) + (fromMaybe x)
f Nothing y (Left a) = (hd y) + a
f (Just x) y (Right b) = (hd y) + (fromMaybe x)
 
hd x = head x
 
tl x = tail x
 