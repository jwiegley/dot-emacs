module PreludeList where

infixr 5 ++
infixl 9  !!
infix 4 `elem`,`notElem`

map f [] = []
map f (x:xs) = f x:map f xs

[]++ys = ys
(x:xs)++ys = x:(xs++ys)

concatMap f = concat . map f

filter p [] = []
filter p (x:xs) = if p x then x:filter p xs else filter p xs

concat = foldr (++) []

null [] = True
null (_:_) = False

head (x:_) = x

tail (_:xs) = xs

foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl f z [] = z
foldl f z (x:xs) = foldl f (f z x) xs

zip (x:xs) (y:ys) = (x,y):zip xs ys
zip _ _ = []

unzip [] = ([],[])
unzip ((x,y):xys) = case unzip xys of (xs,ys) -> (x:xs,y:ys)


length :: [a] -> Int
length [] = 0
length (_:xs) = 1+length xs

replicate n x = take n (repeat x)

repeat x = xs where xs = x:xs

take n xs =
  if n<=0
  then []
  else case xs of
         [] -> []
	 x:xs -> x:take (n-1) xs

drop n xs =
  if n<=0
  then xs
  else case xs of
         [] -> []
	 x:xs -> drop (n-1) xs

all p xs = foldr ((&&).p) True xs
any p xs = foldr ((||).p) False xs

x `elem` xs = any (x==) xs
x `notElem` xs = all (x/=) xs

span p xs = (takeWhile p xs,dropWhile p xs)

takeWhile p [] = []
takeWhile p (x:xs) = if p x then x:takeWhile p xs else []

dropWhile p [] = []
dropWhile p (x:xs) = if p x then dropWhile p xs else x:xs

reverse xs = foldl (\ys y->y:ys) [] xs

foldl1 f (x:xs) = foldl f x xs

minimum xs = foldl1 min xs

lookup :: Eq a => a -> [(a,b)] -> Maybe b
lookup x [] = Nothing
lookup x ((x',y):xys) = if x'==x then Just y else lookup x xys

(!!)                :: [a] -> Int -> a
xs !! n = if n<0
          then error "Prelude.!!: negative index"
	  else case xs of
	         [] -> error "Prelude.!!: index too large"
		 x:xs -> if n==0
			 then x
			 else xs!!(n-1)
