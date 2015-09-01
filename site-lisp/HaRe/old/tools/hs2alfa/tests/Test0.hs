module Test0 where
import Prelude hiding (length,even,odd)

-- Testing literals:
t = 'T'
hello = "Hello, world!"

--answer :: Num a => a
--answer = 42

n = Nothing

tr = True
fa = False

data Nat = Zero | Succ Nat deriving (Eq)

add Zero b = b
add (Succ n) b = Succ (add n b)


length xs = case xs of
              [] -> Zero
	      (x:xs) -> Succ (length xs)

z = length []
sz = Succ z

assert A1 = {length []} === {Zero}
assert A2 = z === {Zero}

even Zero = True
even (Succ n) = odd n

odd Zero = Prelude.False
odd (Succ n) = even n

data Tree a = Leaf a | Node (Tree a) (Tree a)

data App f a = App (f a)

xs = [Nothing,Just ()]

four = let z = Zero
           s x = Succ x
       in s ( s ( s (s z)))

x = id four

--n' = fmap id n
--ys = fmap isJust xs

instance Show Nat
instance Num Nat where
  (+) = add
  --(-) = undefined
  --(*) = undefined
  --fromInteger = undefined

double x = x+x

swap (x,y) = (y,x)

--super x y = (x==y,x<=y)
