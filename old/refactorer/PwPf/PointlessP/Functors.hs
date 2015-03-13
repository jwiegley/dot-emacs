{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

module PointlessP.Functors where

import PointlessP.Combinators

-- Data types as fixed points of functors - PolyP style

class (Functor f) => FunctorOf f d | d -> f
    where inn' :: f d -> d
	  out' :: d -> f d

-- Bridge to data types as explicit fixed points

newtype (Functor f) => Mu f = Mu {unMu :: f (Mu f)}

instance (Functor f) => FunctorOf f (Mu f)
    where inn' = Mu
	  out' = unMu

--infixr 5 :+:
--infixr 6 :*:
--infixr 9 :@:

-- Functors

newtype Id x        = Id {unId :: x}
newtype Const t x   = Const {unConst :: t}
data (PSum g h) x    = Inl (g x) | Inr (h x)
data (PProd g h) x    = PProd (g x) (h x)
newtype (PApp g h) x = Comp {unComp :: g (h x)}

-- Maps

instance Functor Id
    where fmap f (Id x) = Id (f x)

instance Functor (Const t)
    where fmap f (Const x) = Const x

instance (Functor g, Functor h) => Functor (PSum g h)
    where fmap f (Inl x) = Inl (fmap f x)
	  fmap f (Inr x) = Inr (fmap f x)

instance (Functor g, Functor h) => Functor (PProd g h)
    where fmap f (PProd x y) = PProd (fmap f x) (fmap f y)

instance (Functor g, Functor h) => Functor (PApp g h)
    where fmap f (Comp x) = Comp (fmap (fmap f) x)

-- From functors to sums of products

class Rep a b | a -> b
    where to :: a -> b
	  from :: b -> a

instance Rep (Id x) x
    where to (Id x) = x
	  from x = Id x

instance Rep (Const t x) t
    where to (Const t) = t
	  from t = Const t

instance (Rep (g x) y, Rep (h x) z) => Rep ((PSum g h) x) (Either y z)
    where to (Inl a) = Left (to a)
	  to (Inr a) = Right (to a)
	  from (Left a) = Inl (from a)
	  from (Right a) = Inr (from a)

instance (Rep (g x) y, Rep (h x) z) => Rep ((PProd g h) x) (y, z)
    where to (PProd a b) = (to a, to b)
	  from (a, b) = PProd (from a) (from b)

instance (Functor g, Rep (h x) y, Rep (g y) z) => Rep ((PApp g h) x) z
    where to (Comp x) = to (fmap to x) 
	  from y = Comp (fmap from (from y))

-- We also need the (obvious) representation of type functors

instance Rep [a] [a]
    where to = id
	  from = id

-- The out and inn functions

out :: (FunctorOf f d, Rep (f d) fd) => d -> fd
out = to . out'

inn :: (FunctorOf f d, Rep (f d) fd) => fd -> d
inn = inn' . from

ouT :: (FunctorOf f d, Rep (f d) fd) => d -> d -> fd
ouT _ = to . out'

inN :: (FunctorOf f d, Rep (f d) fd) => d -> fd -> d
inN _ = inn' . from

-- Auxiliary definitions

instance FunctorOf (PSum (Const One) (PProd (Const a) Id)) [a] 
    where inn' (Inl (Const _))          = []
	  inn' (Inr (PProd (Const x) (Id xs))) = x:xs
	  out' []     = Inl (Const _L)
	  out' (x:xs) = Inr (PProd (Const x) (Id xs))

nil :: One -> [a]
nil = inn . inl

cons :: (a,[a]) -> [a]
cons = inn . inr

instance FunctorOf (PSum (Const One) Id) Int
    where inn' (Inl (Const _)) = 0
	  inn' (Inr (Id n)) = n+1
	  out' 0     = Inl (Const _L)
	  out' (n+1) = Inr (Id n)

zero :: One -> Int
zero = inn . inl

suck :: Int -> Int
suck = inn . inr 

instance FunctorOf (PSum (Const One) (Const One)) Bool
    where inn' (Inl _) = True
	  inn' (Inr _) = False
	  out' True  = Inl _L
	  out' False = Inr _L

true :: One -> Bool
true = inn . inl

false :: One -> Bool
false = inn . inr

fix :: (a->a) -> a
fix f = f (fix f)
