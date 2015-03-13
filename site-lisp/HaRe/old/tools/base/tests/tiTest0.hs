module TiTest0 where

default(Int)

newtype Id = Id String
newtype F f = F (f Prelude.Int)
newtype F2 f = F2 (f Int Int)


--liftM :: Monad m => (a->b) -> m a -> m b
liftM f m = do x<-m; return (f x)


lnil = length []

data Tags f1 f2 a = (f1 a) :&: (f2 a)

hello = "Hello, world!\n"
hello_again = fmap id hello -- unification when type synonyms are present?

lmap f xs = [f x|x<-xs]
--bla = blaha

a = Id "a"

n = 1
fn = F [n]
fm = F (Just n)
f2a x = F2 (x, x)
f2b x = F2 (Left x)
isNothing x = x==Nothing

--{-
instance Eq a => Eq (Maybe a) where
  Nothing == Nothing = True
  Just x  == Just y  = x==y
  _       == _       = False
--}

--tst = 1==2

l = \ x y z -> let f x = (x,z)
               in let s = f hello
               in (z 'a',f x,f y,s)

not' t = t==False

fnot x = fmap not x

i b x y = if b then x else y

--id :: a -> a

apply = \ f x -> f x

twice f x = f (f x)

--dup :: a -> (a,a)
dup = \ x -> (x,x)

--(id1,id2) = dup id

three = \ x -> [x,x,x]

--ones = (ones,1)

--nomatch = fromJust Nothing :: a

ints = id [1..]

ng b x = let f y = if b then x else y
         in (f, f)


data A a = A a | A2 B
data B = B (A Int)

instance Show a => Show (A a) where
  show (A a) = show a
  show (A2 b) = show b

instance Show B where show (B a) = show a



isZero x | x==0 = True
         | x/=0 = False


happy = [toEnum 0x263a] -- ::String
sad = [toEnum 0x2639]

happy2 = "\x263a"
sad2 = "\x2639"

{-
eq = (==) :: Eq a => a->a->Bool
addff = fst ff+snd ff
-}

ff :: Num a => (a,a)
ff = (four,four)
  where four = 4



fib 0 = 0
fib 1 = 0
fib n = fib (n-1) + fib(n-2)

fac 0 = 1
fac n = n * fac(n-1)
