module MultiDefIn1 where


f :: [Int] -> Int
f x@[] = (hd x) + (hd (tl x))
f x@(b_1 : b_2) = (hd x) + (hd (tl x))
f x = (hd x) + (hd (tl x))

hd = head
tl = tail