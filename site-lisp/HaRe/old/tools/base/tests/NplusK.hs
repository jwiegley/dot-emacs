module NplusK where


pow 0 = 1
pow (n+1) = 2*pow n


f [x,1,y,2] = x+y

g (x,1,y,2) = x+y

(zero+1)=1

z = 0

seven = 6+1
  where n+1 = succ n

{-
instance Eq (a->b)
instance Show (a->b)

instance Num b => Num (a->b) where
  (f+g) x = f x + g x
  (f-g) x = f x - g x
  (f*g) x = f x * g x
  negate f = negate . f
  fromInteger = const . fromInteger
-}
