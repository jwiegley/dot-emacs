module MultiDefIn2 where


f :: [Int] -> Int
f x@[] = (hd x) + (hd (tl x))
f x@(b_1 : b_2) = hd2 + (hd (tl x)) where hd2 = head x
f x = (hd x) + (hd (tl x))

hd = head
tl = tail