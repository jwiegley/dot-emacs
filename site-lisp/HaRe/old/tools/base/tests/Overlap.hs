module Overlap where
--{-
class S a where
  s :: a -> String

instance S String where
  s _ = "String"

instance S a => S [a] where
  s ~[x] = "["++s x++"]"

instance S Char where
  s _ = "Char"

bla = s "Hello"

t x = s [x]

bla2 = t 'a'
--}

data T = T

instance Show [T] where  show _ = "Ts"

instance Show T where show _ = "T"

u :: Show a => a -> String
u x = show ([x],x)

u1 :: Show [a] => a -> String
u1 x = show [x]

bl3 = show [T,T]

bla4 = u T

class    Inject a b where inj :: a -> b
instance Inject a (Either a b) where inj = Left
instance Inject a b => Inject a (Either c b) where inj = Right . inj

type R = Either Char (Either Bool ())

i :: R
i = inj 'a'

b :: R
b = inj False

{-
Inject Bool (Either Char Bool)
<= Inject Bool Bool

-}
