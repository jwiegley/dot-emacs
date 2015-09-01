module Prelude where

id x = x
const x y = x

--type Char = Prelude.Char
--type String = [Char]
--type List a = [a]
data [] a = [] | a : [a]
data () = ()

--type Bool = Prelude.Bool
data Bool = True | False
data Maybe a = Nothing | Just a
data Nat = Zero | Succ Nat
data Either a b = Left a | Right b
n = Nothing

tr = True
fa = False
not b = if b then fa else tr

add Zero b = b
add (Succ n) b = Succ (add n b)

length xs = case xs of
              [] -> Zero
	      (x:xs) -> Succ (length xs)

z = length []

foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

even Zero = True
even (Succ n) = odd n

odd Zero = False
odd (Succ n) = even n

data Tree a = Leaf a | Node (Tree a) (Tree a)

data App f a = App (f a)

xs = [Nothing,Just ()]

four = let z = Zero
           s x = Succ x
       in s ( s ( s (s z)))

map f [] = []
map f (x:xs) = f x:map f xs

x = id four

class Functor f where
  fmap :: (a->b)->f a->f b

class Monad m where
   return :: a -> m a
   (>>=) :: m a -> (a -> m b) -> m b

instance Functor Maybe where
  fmap g m = case m of
	       Nothing -> Nothing
	       Just x -> Just (g x)

instance Functor [] where fmap = map

isJust m = case m of Just x -> True ; Nothing -> False

--n' = fmap id n
ys = fmap isJust xs

class Num a where
  (+) :: a -> a -> a

infixl 6 +

instance Num Nat where
  (+) = add

double x = x+x
