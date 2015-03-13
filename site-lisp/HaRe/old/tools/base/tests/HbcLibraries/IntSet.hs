-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module IntSet (
	IntSet,
	empty, singleton, union, unionMany, add, addMany,
	intersect, delete, deleteMany, minus, 
	-- map, partition, filter, foldl, foldr,
	toList, fromList,
	length, 
	null, isSingleton, intersecting, isSubsetOf, elem
	-- replaceMaybe, substitute
	) where
import Prelude hiding (null,length,elem)
import List(sort)

data IntSet = Nil | Leaf !Int | Fork !IntSet !IntSet
instance Show IntSet where
	--showsType _ = showString "IntSet"
	showsPrec _ Nil = showString "{}"
	showsPrec _ s = showString "{" . f (sort (toList s)) . showString "}"
		where f [x] = shows x
		      f (x:xs) = shows x . showString ", " . f xs

instance Eq IntSet where
	Nil == Nil = True
	Leaf x == Leaf x' = x == x'
	Fork l r == Fork l' r' = l == l' && r == r'
	_ == _ = False

empty :: IntSet
empty = Nil

singleton :: Int -> IntSet
singleton x = Leaf x

null :: IntSet -> Bool
null Nil = True
null (Leaf _) = False
null (Fork _ _) = False

add :: Int -> IntSet -> IntSet
add x Nil = Leaf x
add x s@(Leaf x') =
	if x == x' then
	    s
	else
	    add x (add x' (Fork Nil Nil))
add x (Fork l r) =
	if odd x then
	    Fork l (add (x `div` 2) r)
	else
	    Fork (add (x `div` 2) l) r

addMany :: [Int] -> IntSet -> IntSet
addMany is s = foldr add s is

elem :: Int -> IntSet -> Bool
elem x Nil = False
elem x (Leaf x') = x == x'
elem x (Fork l r) =
	if odd x then
	    elem (x `div` 2) r
	else
	    elem (x `div` 2) l

union :: IntSet -> IntSet -> IntSet
union Nil t = t
union (Leaf x) t = add x t
union t Nil = t
union t (Leaf x) = add x t
union (Fork l r) (Fork l' r') = Fork (union l l') (union r r')

unionMany :: [IntSet] -> IntSet
unionMany ss = foldr union empty ss

delete :: Int -> IntSet -> IntSet
delete x Nil = Nil
delete x t@(Leaf x') = if x == x' then Nil else t
delete x (Fork l r) =
	if odd x then
	    fork l (delete (x `div` 2) r)
	else
	    fork (delete (x `div` 2) l) r

deleteMany :: [Int] -> IntSet -> IntSet
deleteMany is s = foldr delete s is

fork Nil Nil = Nil
fork Nil (Leaf x) = Leaf (x*2+1)
fork (Leaf x) Nil = Leaf (x*2)
fork l r = Fork l r

intersect :: IntSet -> IntSet -> IntSet
intersect Nil _ = Nil
intersect t@(Leaf x) t' = if elem x t' then t else Nil
intersect _ Nil = Nil
intersect t t'@(Leaf x) = if elem x t then t' else Nil
intersect (Fork l r) (Fork l' r') = fork (intersect l l') (intersect r r')

fromList :: [Int] -> IntSet
fromList xs = foldr add empty xs

toList :: IntSet -> [Int]
toList Nil = []
toList (Leaf x) = [x]
toList (Fork l r) = map (2*) (toList l) ++ map ((1+).(2*)) (toList r)

isSubsetOf :: IntSet -> IntSet -> Bool
isSubsetOf Nil _ = True
isSubsetOf (Leaf x) t = elem x t
isSubsetOf (Fork l r) (Fork l' r') = isSubsetOf l l' && isSubsetOf r r'
isSubsetOf _ _ = False

minus :: IntSet -> IntSet -> IntSet
minus t Nil = t
minus t (Leaf x) = delete x t
minus Nil _ = Nil
minus t@(Leaf x) t' = if elem x t' then Nil else t
minus (Fork l r) (Fork l' r') = fork (minus l l') (minus r r')

length :: IntSet -> Int
length Nil = 0
length (Leaf _) = 1
length (Fork l r) = length l + length r

isSingleton s = length s == 1

intersecting x y = not (null (intersect x y))
