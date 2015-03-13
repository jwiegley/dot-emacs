module Subsequences(suffixes, prefixes, subsequences, permutations, subsequence, isPrefixOf, isSuffixOf, isSubsequenceOf, isPermutationOf, isPrefixOfBy, isSuffixOfBy, isSubsequenceOfBy, isPermutationOfBy, locateSubsequences) where

suffixes :: [a] -> [[a]]
suffixes []         = []
suffixes xxs@(_:xs) = xxs : suffixes xs

prefixes :: [a] -> [[a]]
prefixes [] = []
prefixes xs = xs : prefixes (init xs)

subsequences :: [a] -> [[a]]
subsequences = concatMap prefixes . suffixes

permutations :: [a] -> [[a]]
permutations [] = [[]]
permutations (x:xs) = [ zs | ys <- permutations xs, zs <- insertAll x ys ]
	where insertAll x [] = [[x]]
	      insertAll x yys@(y:ys) = (x:yys) : map (y:) (insertAll x ys)

subsequence :: Int -> Int -> [a] -> [a]
subsequence start end xs = take (end - start) (drop start xs)

isPrefixOf, isSuffixOf :: Eq a => [a] -> [a] -> Bool
isSubsequenceOf, isPermutationOf :: Eq a => [a] -> [a] -> Bool
isPrefixOf = isPrefixOfBy (==)
isSuffixOf = isSuffixOfBy (==)
isSubsequenceOf = isSubsequenceOfBy (==)
isPermutationOf = isPermutationOfBy (==)

isPrefixOfBy, isSuffixOfBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
isSubsequenceOfBy, isPermutationOfBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
isPrefixOfBy eq []     ys = True
isPrefixOfBy eq (x:xs) (y:ys) | eq x y = isPrefixOfBy eq xs ys
isPrefixOfBy eq _      _ = False
isSuffixOfBy eq xs ys = isPrefixOfBy eq (reverse xs) (reverse ys)
isSubsequenceOfBy eq xs ys = any (isPrefixOfBy eq xs) (suffixes ys)
isPermutationOfBy eq [] [] = True
isPermutationOfBy eq (x:xs) ys = del x ys []
	where del x [] _ = False
	      del x (y:ys) r =  if eq x y then isPermutationOfBy eq xs (reverse r ++ ys) 
	      			else del x ys (y:r)

locateSubsequences   :: Eq a => [a] -> [a] -> [Int]
locateSubsequences xs ys = locateSubsequencesBy (==) xs ys
locateSubsequencesBy :: (a -> a -> Bool) -> [a] -> [a] -> [Int]
locateSubsequencesBy eq xs ys =
	map fst (filter (isPrefixOfBy eq xs . snd) (zip [0..] (suffixes ys)))
