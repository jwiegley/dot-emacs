
class P a where
 foo :: a 


instance P () where
  foo  = ()


data (P a, Q a) => X a = B [a]



a = B[()]

(a,b) = B[()]
[C a b, A (b,B c), c,b] = B[()]

f x y = x + y
x + y = x * y
(x+y) = 4

