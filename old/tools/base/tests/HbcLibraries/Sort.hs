module Sort(sort,sortLe) where

sort xs = sortLe (<=) xs

sortLe :: (a -> a -> Bool) -> [a] -> [a]
sortLe le l = tmsort le l

--sort :: (Ord a) => [a] -> [a]
--sort l = tmsort (<=) l

tmsort _ [] = []
tmsort _ [x] = [x]		-- just for speed
tmsort le (x:xs) = msort le (upSeq le xs [x])

upSeq _  [] xs = [reverse xs]
upSeq le (y:ys) xxs@(x:xs) =
	if le x y then
	    upSeq le ys (y:xxs)
	else
	    reverse xxs : upSeq le ys [y]

msort _ [xs] = xs
msort le xss = msort le (mergePairs le xss)

mergePairs le (xs:ys:xss) = merge le xs ys : mergePairs le xss
mergePairs _  xss = xss

merge le xxs@(x:xs) yys@(y:ys) =
	if le x y then
	    x:merge le xs yys
	else
	    y:merge le xxs ys
merge _  []         yys = yys
merge _  xxs        []  = xxs
