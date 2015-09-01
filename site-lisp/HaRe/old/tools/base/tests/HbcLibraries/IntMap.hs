-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module IntMap (
	IntMap, 
	empty, singleton, union, unionMany, add, (//), addKeep,
	-- union_C, unionMany_C, addMany_C,
	add_C,
	-- intersect, 
	delete, deleteMany, 
	--minus, 
	foldr, imap, filter,
	-- partition, foldl,
	toList, fromList,
	length,
	null, isSingleton,
	-- intersecting, subset
	elems, indices,
	(!),
	lookup, lookupWithDefault --, lookupWithContinuation
	) where

-- @@ Mapping from Int to any type.  Similar to an array with Int index, but
-- @@ without any bounds on the index.

import Prelude hiding (foldr,length,lookup,filter,null)
import qualified Prelude

data IntMap a = Nil | Leaf !Int a | Fork !(IntMap a) !(IntMap a)
instance (Show a) => Show (IntMap a) where
	--showsType _ = showString "IntMap a"
	showsPrec _ Nil = showString "{}"
	showsPrec _ s = showString "{" . f (toList s) . showString "}"
		where f [x] = g x
		      f (x:xs) = g x . showString ", " . f xs
		      g (i, r) = shows i . showString "->" . shows r

instance (Eq a) => Eq (IntMap a) where
	Nil == Nil = True
	Leaf x y == Leaf x' y' = x == x' && y == y'
	Fork l r == Fork l' r' = l == l' && r == r'
	_ == _ = False

empty :: IntMap a
empty = Nil

singleton :: (Int, a) -> IntMap a
singleton (x, y) = Leaf x y

null :: IntMap a -> Bool
null Nil = True
null (Leaf _ _) = False
null (Fork _ _) = False

add :: (Int, a) -> IntMap a -> IntMap a
add (x, y) t = add' x y t
add' :: Int -> a -> IntMap a -> IntMap a
add' x y Nil = Leaf x y
add' x y (Leaf x' y') =
	if x == x' then
	    Leaf x y
	else
	    add' x y (add' x' y' (Fork Nil Nil))
add' x y (Fork l r) =
	if odd x then
	    Fork l (add' (x `div` 2) y r)
	else
	    Fork (add' (x `div` 2) y l) r

-- similar to add, but does not overwrite the old contents
addKeep :: (Int, a) -> IntMap a -> IntMap a
addKeep (x, y) t = addKeep' x y t
addKeep' :: Int -> a -> IntMap a -> IntMap a
addKeep' x y Nil = Leaf x y
addKeep' x y t@(Leaf x' y') =
	if x == x' then
	    t
	else
	    addKeep' x y (addKeep' x' y' (Fork Nil Nil))
addKeep' x y (Fork l r) =
	if odd x then
	    Fork l (addKeep' (x `div` 2) y r)
	else
	    Fork (addKeep' (x `div` 2) y l) r

lookupWithDefault :: IntMap a -> a -> Int -> a
lookupWithDefault Nil d x = if x==x then d else d			-- force it to be strict in x
lookupWithDefault (Leaf x' y) d x = if x == x' then y else d
lookupWithDefault (Fork l r) d x =
	if odd x then
	    lookupWithDefault r d (x `div` 2)
	else
	    lookupWithDefault l d (x `div` 2)

lookup :: Int -> IntMap a -> Maybe a
lookup x Nil = Nothing
lookup x (Leaf x' y) = if x == x' then Just y else Nothing
lookup x (Fork l r) =
	if odd x then
	    lookup (x `div` 2) r
	else
	    lookup (x `div` 2) l

(!) :: IntMap a -> Int -> a
t ! x = case lookup x t of Nothing -> error "IntMap.!: index not found"; Just y -> y


union :: IntMap a -> IntMap a -> IntMap a
union Nil t = t
union (Leaf x y) t = add' x y t
union t Nil = t
union t (Leaf x y) = addKeep' x y t
union (Fork l r) (Fork l' r') = Fork (union l l') (union r r')

unionMany :: [IntMap a] -> IntMap a
unionMany = Prelude.foldr union empty

fromList :: [(Int, a)] -> IntMap a
fromList xs = Prelude.foldr (\ (x,y) -> \ m -> add' x y m) empty xs

toList :: IntMap a -> [(Int, a)]
toList t = foldr (:) [] t
{-
toList :: IntMap a -> [(Int, a)]
toList Nil = []
toList (Leaf x y) = [(x, y)]
toList (Fork l r) = [(2*x, y) | (x, y) <- toList l] ++ [ (2*x+1, y) | (x, y) <- toList r]
-}

elems :: IntMap a -> [a]
elems = Prelude.map snd . toList

indices :: IntMap a -> [Int]
indices = Prelude.map fst . toList

length :: IntMap a -> Int
length Nil = 0
length (Leaf _ _) = 1
length (Fork l r) = length l + length r

isSingleton :: IntMap a -> Bool
isSingleton t = length t == 1

add_C :: (a->a->a) -> (Int, a) -> IntMap a -> IntMap a
add_C comb (x, y) t = add_C' comb x y t
add_C' :: (a->a->a) -> Int -> a -> IntMap a -> IntMap a
add_C' comb x y Nil = Leaf x y
add_C' comb x y (Leaf x' y') =
	if x == x' then
	    Leaf x (comb y y')
	else
	    add_C' comb x y (add_C' comb x' y' (Fork Nil Nil))
add_C' comb x y (Fork l r) =
	if odd x then
	    Fork l (add_C' comb (x `div` 2) y r)
	else
	    Fork (add_C' comb (x `div` 2) y l) r

(//) :: IntMap a -> [(Int, a)] -> IntMap a
t // [] = t
t // ((x,y):xys) = add' x y t // xys

instance Functor IntMap where
    fmap f Nil = Nil
    fmap f (Leaf x y) = Leaf x (f y)
    fmap f (Fork l r) = Fork (fmap f l) (fmap f r)

delete :: Int -> IntMap a -> IntMap a
delete x Nil           = Nil
delete x t@(Leaf x' y) = if x == x' then Nil else t
delete x (Fork l r)    = if odd x then
                             fork l (delete (x `div` 2) r)
			 else
			     fork (delete (x `div` 2) l) r

deleteMany :: [Int] -> IntMap a -> IntMap a
deleteMany is s = Prelude.foldr delete s is

fork Nil        Nil        = Nil
fork Nil        (Leaf x y) = Leaf (x*2+1) y
fork (Leaf x y) Nil        = Leaf (x*2) y
fork l          r          = Fork l r

foldr :: ((Int, a) -> b -> b) -> b -> IntMap a -> b
foldr f z Nil = z
foldr f z (Leaf x y) = f (x,y) z
foldr f z (Fork l r) = foldr g (foldr h z r) l
    where g (x,y) z = f (2*x,y) z
          h (x,y) z = f (2*x+1,y) z

imap :: ((Int, a) -> (Int, b)) -> IntMap a -> IntMap b
imap f t = foldr (add . f) empty t

filter :: ((Int, a) -> Bool) -> IntMap a -> IntMap a
filter p t = foldr (\x l -> if p x then add x l else l) empty t
