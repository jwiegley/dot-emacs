-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module OrdMap(
	OrdMap,
	empty, singleton, union, unionMany, add, (//),
	-- addKeep, union_C, unionMany_C, addMany_C, add_C,
	-- intersect, delete, deleteMany, minus, 
	-- partition, filter, foldl, foldr
	toList, fromList,
	length,
	null, isSingleton,
	-- intersecting, subset
	elems, indices,
	--(!),
	lookup, lookupWithDefault --, lookupWithContinuation
	) where
import Prelude hiding (lookup,length,null)
	
-- @@ Finite mappings with ordered keys.

-- Red-Black trees.
-- Implementation based on work by Norris Boyd, Andrew W. Appel,
-- David R. Tarditi, and Stephen J. Bevan.

data Colour = Red | Black

data OrdMap a b
    = Empty
    | Node a b Colour (OrdMap a b) (OrdMap a b)

instance (Ord a, Show a, Show b) => Show (OrdMap a b) where
{-  #ifdef __HBC__
	showsType x = showString "(OrdMap " . showsType (f x) . showString " " . showsType (g x) . showString ")"
		where f :: (Ord a) => OrdMap a b -> a
		      f _ = error "OrdMap.f"
		      g :: (Ord a) => OrdMap a b -> b
		      g _ = error "OrdMap.g"
-}
-- #else
        showsPrec _ om = showString "<OrdMap>"
-- #endif

instance (Ord a, Eq b) => Eq (OrdMap a b) where
	x == y  =  toList x == toList y

rbiR :: a -> b -> OrdMap a b -> OrdMap a b -> OrdMap a b
rbiR k v (Node sk sv Red sl@(Node _ _ Red _ _) sr) (Node lk lv Red ll lr) =
    Node k v Red (Node lk lv Black ll lr) (Node sk sv Black sl sr)

rbiR k v (Node sk sv Red sl sr@(Node _ _ Red _ _)) (Node lk lv Red ll lr) =
    Node k v Red (Node lk lv Black ll lr) (Node sk sv Black sl sr)

rbiR k v (Node sk sv Red sl@(Node slk slv Red sll slr) sr) l =
    Node slk slv Black (Node k v Red l sll) (Node sk sv Red slr sr)

rbiR k v (Node sk sv Red sl sr@(Node _ _ Red _ _)) l =
    Node sk sv Black (Node k v Red l sl) sr

rbiR k v t l = Node k v Black l t

rbiL :: a -> b -> OrdMap a b -> OrdMap a b -> OrdMap a b
rbiL k v (Node lk lv Red ll lr@(Node _ _ Red _ _)) (Node rk rv Red rl rr) =
    Node k v Red (Node lk lv Black ll lr) (Node rk rv Black rl rr)

rbiL k v (Node lk lv Red ll@(Node _ _ Red _ _) lr) (Node rk rv Red rl rr) =
    Node k v Red (Node lk lv Black ll lr) (Node rk rv Black rl rr)

rbiL k v (Node lk lv Red ll lr@(Node lrk lrv Red lrl lrr)) r =
    Node lrk lrv Black (Node lk lv Red ll lrl) (Node k v Red lrr r)

rbiL k v (Node lk lv Red ll@(Node llk llv Red lll llr) lr) r =
    Node lk lv Black ll (Node k v Red lr r)

rbiL k v t r = Node k v Black t r

rbi :: (Ord a) => a -> b -> OrdMap a b -> OrdMap a b
rbi e v Empty = Node e v Red Empty Empty
rbi e v t@(Node k w Black l r) =
	if e <= k then
	    if e == k then
		Node e v Black l r
	    else
		rbiL k w (rbi e v l) r
	else
	    rbiR k w (rbi e v r) l
rbi e v t@(Node k w Red l r) =
	if e <= k then
	    if e == k then
		Node e v Red l r
	    else
		Node k w Red (rbi e v l) r
	else
	    Node k w Red l (rbi e v r)

-- Empty table.
empty :: OrdMap a b
empty = Empty

singleton :: (Ord a) => (a, b) -> OrdMap a b
singleton (k, v) = Node k v Black Empty Empty

null :: OrdMap a b -> Bool
null Empty = True
null _ = False

length :: OrdMap a b -> Int
length Empty = 0
length (Node _ _ _ l r) = 1 + length l + length r

isSingleton :: OrdMap a b -> Bool
isSingleton (Node _ _ _ Empty Empty) = True
isSingleton _ = False

elems :: OrdMap a b -> [b]
elems Empty = []
elems (Node k v _ l r) = elems l ++ v : elems r

indices :: OrdMap a b -> [a]
indices Empty = []
indices (Node k v _ l r) = indices l ++ k : indices r

union :: (Ord a) => OrdMap a b -> OrdMap a b -> OrdMap a b
union t1 t2 = union' t1 (toList t2)
union' t [] = t
union' t (xy:xys) = union' (add xy t) xys

unionMany :: (Ord a) => [OrdMap a b] -> OrdMap a b
unionMany = foldr union empty

-- Insert an element overwriting an existing one with the same key.
add :: (Ord a) => (a,  b) -> OrdMap a b -> OrdMap a b
add (e, v) t =
    case rbi e v t of
        Node k v Red l@(Node _ _ Red _ _) r -> Node k v Black l r
        Node k v Red l r@(Node _ _ Red _ _) -> Node k v Black l r
        x                                   -> x

(//) :: (Ord a) => OrdMap a b -> [(a, b)] -> OrdMap a b
t // [] = t
t // (xy:xys) = add xy t // xys

-- Look up an element.
lookup :: (Ord a) => a -> OrdMap a b -> Maybe b
lookup _ Empty = Nothing
lookup e (Node k v _ l r) =
	if e <= k then
	    if e == k then Just v
	    else lookup e l
	else lookup e r

-- Map a function over the values.
instance (Ord a) => Functor (OrdMap a) where
    --map :: (b->c) -> OrdMap a b -> OrdMap a c
    fmap f Empty = Empty
    fmap f (Node k v c l r) = Node k (f v) c (fmap f l) (fmap f r)

lookupWithDefault :: (Ord a) => OrdMap a b -> b -> a -> b
lookupWithDefault Empty d _ = d
lookupWithDefault (Node k v _ l r) d e =
	if e <= k then 
	    if e == k then v
	    else lookupWithDefault l d e
	else lookupWithDefault r d e

fromList :: (Ord a) => [(a,b)] -> OrdMap a b
fromList l = union' empty l

toList :: OrdMap a b -> [(a, b)]
toList Empty = []
toList (Node k v _ l r) = toList l ++ (k,v) : toList r

