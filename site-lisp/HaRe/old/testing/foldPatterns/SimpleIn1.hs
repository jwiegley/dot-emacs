module SimpleIn1 where



f :: [Int] -> Int
f y@(z:zs) = hd y + hd (tl y)


hd x = head x
tl x = tail x
