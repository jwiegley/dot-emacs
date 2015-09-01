module Sort where

--insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = if x<=y
		  then x:y:ys
		  else y:insert x ys

--sort :: Ord a => [a] -> [a]
sort [] = []
sort (x:xs) = insert x (sort xs)

isort xs = foldr insert [] xs
