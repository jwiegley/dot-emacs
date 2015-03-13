module SimpleIn1 where
f :: [Int] -> Int
 
f y =   case y of
            y@[] -> (hd y) + (hd (tl y))
            y@(b_1 : b_2) -> (hd y) + (hd (tl y))
f y = (hd y) + (hd (tl y))
 
hd x = head x
 
tl x = tail x
 