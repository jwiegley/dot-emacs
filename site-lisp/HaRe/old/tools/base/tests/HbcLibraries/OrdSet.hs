-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module OrdSet (
	OrdSet,
	empty, singleton, union, unionMany, add, addMany,
	-- intersect, delete, deleteMany, minus, 
	-- map, partition, filter, foldl, foldr,
	toList, fromList,
	length, 
	null, isSingleton, 
	-- intersecting, isSubsetOf, 
	elem
	-- replaceMaybe, substitute
	) where
import Prelude hiding (null,length,elem)

-- @@ Sets of ordered items.

-- Red-Black trees.
-- Implementation based on work by Norris Boyd, Andrew W. Appel,
-- David R. Tarditi, and Stephen J. Bevan.

data Colour = Red | Black deriving (Eq)

data OrdSet a
    = Empty
    | Node a Colour (OrdSet a) (OrdSet a)

instance (Eq a) => Eq (OrdSet a) where -- different trees may represent equal sets (XX ?)
    s1 == s2 = toList s1 == toList s2

instance (Ord a, Show a) => Show (OrdSet a) where
	showsPrec p x = showString "OrdSet:" . showsPrec p (toList x)
{-
	showsType x = showString "(OrdSet " . showsType (f x) . showString ")"
		where f :: (Ord a) => OrdSet a -> a
		      f _ = error "OrdSet.f"
-}
rbiR :: a -> OrdSet a -> OrdSet a -> OrdSet a
rbiR k (Node sk Red sl@(Node _ ed _ _) sr) (Node lk Red ll lr) =
    Node k Red (Node lk Black ll lr) (Node sk Black sl sr)

rbiR k (Node sk Red sl sr@(Node _ Red _ _)) (Node lk Red ll lr) =
    Node k Red (Node lk Black ll lr) (Node sk Black sl sr)

rbiR k (Node sk Red sl@(Node slk Red sll slr) sr) l =
    Node slk Black (Node k Red l sll) (Node sk Red slr sr)

rbiR k (Node sk Red sl sr@(Node _ Red _ _)) l =
    Node sk Black (Node k Red l sl) sr

rbiR k t l = Node k Black l t

rbiL :: a -> OrdSet a -> OrdSet a -> OrdSet a
rbiL k (Node lk Red ll lr@(Node _ Red _ _)) (Node rk Red rl rr) =
    Node k Red (Node lk Black ll lr) (Node rk Black rl rr)

rbiL k (Node lk Red ll@(Node _ Red _ _) lr) (Node rk Red rl rr) =
    Node k Red (Node lk Black ll lr) (Node rk Black rl rr)

rbiL k (Node lk Red ll lr@(Node lrk Red lrl lrr)) r =
    Node lrk Black (Node lk Red ll lrl) (Node k Red lrr r)

rbiL k (Node lk Red ll@(Node llk Red lll llr) lr) r =
    Node lk Black ll (Node k Red lr r)

rbiL k t r = Node k Black t r

rbi :: (Ord a) => a -> OrdSet a -> OrdSet a
rbi e Empty = Node e Red Empty Empty
rbi e t@(Node k Black l r) =
	if e <= k then
	    if e == k then
		Node e Black l r
	    else
		rbiL k (rbi e l) r
	else
	    rbiR k (rbi e r) l
rbi e t@(Node k Red l r) =
	if e <= k then
	    if e == k then
		Node e Red l r
	    else
		Node k Red (rbi e l) r
	else
	    Node k Red l (rbi e r)

-- Empty table.
empty :: OrdSet a
empty = Empty

singleton :: a -> OrdSet a
singleton k = Node k Black Empty Empty

-- XXX awful!
union :: (Ord a) => OrdSet a -> OrdSet a -> OrdSet a
union t1 t2 =
	f t2 (toList' t1 [])
	where f t [] = t
	      f t (x:xs) =
		case add x t of	-- just to force evaluation to avoid space leak
		Empty -> error "union"
		t' -> f t' xs

unionMany :: (Ord a) => [OrdSet a] -> OrdSet a
unionMany ts = foldr union empty ts

add :: (Ord a) => a -> OrdSet a -> OrdSet a
add e t =
    case rbi e t of
        Node k Red l@(Node _ Red _ _) r -> Node k Black l r
        Node k Red l r@(Node _ Red _ _) -> Node k Black l r
        x                               -> x

addMany :: (Ord a) => [a] -> OrdSet a -> OrdSet a
addMany is s = foldr add s is

-- Look up an element.
elem :: (Ord a) => a -> OrdSet a -> Bool
elem _ Empty = False
elem e (Node k _ l r) =
	if e <= k then
	    e == k || elem e l
	else elem e r

fromList :: (Ord a) => [a] -> OrdSet a
fromList l = foldr add Empty l

toList t = toList' t []
toList' Empty xs = xs
toList' (Node k _ l r) xs = toList' l (k : toList' r xs)

null Empty = True
null _ = False

isSingleton :: OrdSet a -> Bool
isSingleton (Node _ _ Empty Empty) = True
isSingleton _ = False

length :: OrdSet a -> Int
length Empty = 0
length (Node _ _ l r) = 1 + length l + length r
