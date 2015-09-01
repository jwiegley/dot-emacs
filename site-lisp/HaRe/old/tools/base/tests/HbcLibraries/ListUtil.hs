module ListUtil{-(
	assoc, concatMap, unfoldr, mapAccuml, union, intersection,
	chopList, assocDef, lookup, module Maybe,
        rept, tails, groupEq, group, readListLazily, nubEq, elemEq,
	mix, mapFst,mapSnd)-} where

--   Now report says that it is not ok to hide not exported entries
import Prelude -- hiding (unfoldr) 
               
import Maybe
import List hiding (union,tails,unfoldr)

breakAt :: (Eq a) => a -> [a] -> ([a], [a])
breakAt _ [] = ([], [])
breakAt x (x':xs) =
	if x == x' then
	    ([], xs)
	else
	    let (ys, zs) = breakAt x xs
	    in  (x':ys, zs)

-- Read a list lazily (in contrast with reads which requires
-- to see the ']' before returning the list.
readListLazily :: (Read a) => String -> [a]
readListLazily cs = 
    case lex cs of
      [("[",cs)] -> readl' cs
      _          -> error "No leading '['"
    where readl' cs  =
                case reads cs of
                  [(x,cs)]  -> x : readl cs
                  []        -> error "No parse for list element"
                  _         -> error "Ambigous parse for list element"
          readl cs =
                case lex cs of
                  [("]",_)]  -> []
                  [(",",cs)] -> readl' cs
                  _          -> error "No ',' or ']'"

-- Lookup an item in an association list.  Apply a function to it if it is found, otherwise return a default value.
assoc :: (Eq c) => (a -> b) -> b -> [(c, a)] -> c -> b
assoc f d [] x                       = d
assoc f d ((x',y):xys) x | x' == x   = f y
                         | otherwise = assoc f d xys x

-- Repeatedly extract (and transform) values until a predicate hold.  Return the list of values.
unfoldr :: (a -> (b, a)) -> (a -> Bool) -> a -> [b]
unfoldr f p x | p x       = []
	      | otherwise = y:unfoldr f p x'
			      where (y, x') = f x

-- Map, but plumb a state through the map operation.
mapAccuml :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccuml f s []     = (s, [])
mapAccuml f s (x:xs) = (s'', y:ys)
		       where (s',  y)  = f s x
			     (s'', ys) = mapAccuml f s' xs

-- Union of sets as lists.
union :: (Eq a) => [a] -> [a] -> [a]
union xs ys = xs ++ (ys \\ xs)

-- Intersection of sets as lists.
intersection :: (Eq a) => [a] -> [a] -> [a]
--intersection xs ys = [x | x<-xs, x `elem` ys]
intersection xs ys = filter (\x -> x `elem` ys) xs

--- Functions derived from those above

chopList :: ([a] -> (b, [a])) -> [a] -> [b]
chopList f l = unfoldr f null l

assocDef :: (Eq a) => [(a, b)] -> b -> a -> b
assocDef l d x = assoc id d l x

--lookup :: (Eq a) => [(a, b)] -> a -> Maybe b
--lookup l x = assoc (\x -> Just x) Nothing l x

-- Repeat an element n times
--rept :: (Integral a) => a -> b -> [b]
rept 0 _ = []
rept n x = x : rept (n-1) x
--rept n x = if n<=0 then [] else x:rept (n-1) x

-- Take all the tails
tails :: [a] -> [[a]]
tails []         = []
tails xxs@(_:xs) = xxs : tails xs

{-
-- group list elements according to an equality predicate
groupEq :: (a->a->Bool) -> [a] -> [[a]]
groupEq eq xs = chopList f xs
		where f xs@(x:_) = span (eq x) xs

group :: (Eq a) => [a] -> [[a]]
group xs = groupEq (==) xs

-- Read a list lazily (in contrast with reads which requires
-- to see the ']' before returning the list.
readListLazily :: (Text a) => String -> [a]
readListLazily cs = 
    case lex cs of
      [("[",cs)] -> readl' cs
      _          -> error "No leading '['"
    where readl' cs  =
                case reads cs of
                  [(x,cs)]  -> x : readl cs
                  []        -> error "No parse for list element"
                  _         -> error "Ambigous parse for list element"
          readl cs =
                case lex cs of
                  [("]",_)]  -> []
                  [(",",cs)] -> readl' cs
                  _          -> error "No ',' or ']'"


nubEq :: (a->a->Bool) -> [a] -> [a]
nubEq eq l = nub' l []
	where nub' [] _	    = []
	      nub' (x:xs) l = if elemEq eq x l then nub' xs l else x : nub' xs (x:l)
-}
elemEq :: (a->a->Bool) -> a -> [a] -> Bool
elemEq eq _ []	   = False
elemEq eq x (y:ys) = eq x y || elemEq eq x ys

{-
--{-# SPECIALIZE average :: [Float] -> Float, [Double] -> Double #-}
average :: (Fractional a) => [a] -> a
average xs = f xs 0 0
	where f []     s l = s / fromInt l
	      f (x:xs) s l = f xs (s+x) (l+1)
fromInt = id
-}

mix [] y = []
mix [x] y = x
mix (x:xs) y = x ++ y ++ mix xs y

mapFst f [] = []
mapFst f ((x,y):zs) = (f x,y):mapFst f zs

mapSnd f [] = []
mapSnd f ((x,y):zs) = (x,f y):mapSnd f zs
