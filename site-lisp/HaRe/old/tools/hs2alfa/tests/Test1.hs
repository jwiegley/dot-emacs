module Test1 where


b = Nothing == Just True

--t = (\x->[x]) True
t2 = (:[]) True
t3 = (True:) []

succ = (+1)

short xs = null (drop 1 xs)

(x,y) = bla

bla = (False,if True then  True else False)

--swap = \ (x,y) -> (y,x)

zip2 (x:xs) (y:ys) = (x,y):zip2 xs ys
zip2 _ _ = []

unzip4                  =  foldr (\(a,b,c,d) ~(as,bs,cs,ds) ->
                                        (a:as,b:bs,c:cs,d:ds))
                                 ([],[],[],[])

partition               :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs =  foldr select ([],[]) xs
   where select x (ts,fs) | p x = (x:ts,fs)
                          | otherwise = (ts, x:fs)

intersperse             :: a -> [a] -> [a]
intersperse sep []      =  []
intersperse sep [x]     =  [x]
intersperse sep (x:xs)  =  x : sep : intersperse sep xs

mem x [] = True
mem x (y:ys) = x==y && mem x ys
