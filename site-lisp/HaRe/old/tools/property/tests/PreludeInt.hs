module PreludeInt where

-- 32-bit Int:
newtype HInt = Int (Two (Two (Two (Two (Two Bit))))) deriving (Eq)
-- 4-bit Int:
--newtype HInt = Int (Two (Two Bit)) deriving (Eq)
-- 2-bit Int:
--newtype Int = Int (Two Bit) deriving (Eq{-,Show-})

data Two a = Two a a deriving (Eq)
data Bit = O | I deriving (Eq)

xor O O = O
xor I I = O
xor _ _ = I

--instance Show a=>Show (Two a) where
--  showsPrec n (Two a b) = showsPrec n a . showsPrec n b

class BitOps a where
  add :: Bit -> a -> a -> (a,Bit)
  one,zero :: a
--size :: a->Int
  msb :: a -> Bit
  invert :: a->a

m1 :: BitOps a => a
m1 = invert zero

instance BitOps Bit where
  add O O O = (O,O)
  add O O I = (I,O)
  add O I O = (I,O)
  add O I I = (O,I)
  add I O O = (I,O)
  add I O I = (O,I)
  add I I O = (O,I)
  add I I I = (I,I)

  zero = O
  one = I
--size _ = 1
  msb b = b

  invert O = I
  invert I = O

instance BitOps a => BitOps (Two a) where
  add c0 (Two x2 x1) (Two y2 y1) = (Two z2 z1,c2)
     where
       (z1,c1) = add c0 x1 y1
       (z2,c2) = add c1 x2 y2

  zero = Two zero zero
  one = Two zero one
--size ~(Two a _) = 2*size a
  msb (Two a _) = msb a
  invert (Two a b) = Two (invert a) (invert b)

instance BitOps HInt where
  add c0 (Int x) (Int y) = (Int z,c1)
     where (z,c1) = add c0 x y
  zero = Int zero
  one = Int one
--size (Int a) = size a
  msb (Int a) = msb a
  invert (Int a) = Int (invert a)

complement x = fst (add I zero (invert x))
add1 a b = fst (add O a b)

class BitOps a => Mul a where mul :: a->a->Two a

instance Mul Bit where
  mul O _ = Two O O
  mul I b = Two O b

instance Mul a => Mul (Two a) where
 mul (Two x2 x1) (Two y2 y1) = Two (Two z4 z3) (Two z2 z1)
  where
    Two z2a z1  = mul x1 y1
    Two z3a z2b = mul x1 y2
    Two z3b z2c = mul x2 y1
    Two z4a z3c = mul x2 y2
    (z2ab,c1)   = add O z2a z2b
    (z2,c2)     = add c1 z2ab z2c
    (z3ab,c3)   = add c2 z3a z3b
    (z3,c4)     = add c3 z3ab z3c
    (z4,O)      = add c4 z4a zero

{-
 -- (2*x2+x1)*(2*y2+y1) = 4*x2*y2 + 2*x2*y1 + 2*x1*y2 + x1*y1

 --  ab
     cd
 --------
     bd
    ad 
    bc
   ac
-}

mul1 a b = c where Two _ c = mul a b
babs b =  if msb b==I then complement b else b
bsignum b = if msb b==I then m1 else if b==zero then zero else one

smul x = mul1 x
--smul a b = if msb a `xor` msb b ==I then complement p else p
--   where p = mul1 (babs a) (babs b)

instance Mul HInt where
 mul (Int a) (Int b) = Two zero (Int (smul a b))
{-
instance Num Bit where
  --fromInteger n = if even n then O else I
  (+) = add1
  negate = complement
  (*) = smul
  abs = babs

instance (Mul a,BitOps a,Num a) => Num (Two a) where
{-
  fromInteger n = Two b a
    where a = fromInteger n
          s = size a
          b = fromInteger (n `div` (2^s))
-}
  (+) = add1
  negate = complement
  (*) = smul
  abs = babs
  signum = bsignum
-}
{-P:
instance Num HInt where

  fromInteger = primFromInteger
  (+) = add1
  negate = complement
  (*) = smul
  abs = babs
  signum = bsignum
-}


two,four,eight,ten :: HInt
two=add1 one one
four=add1 two two
eight=add1 four four
ten=add1 eight two

{-P:
primFromInteger i =  if primIntegerNeg i then complement d else d
  where d = fromDigits zero (primIntegerDigits i)
-}

fromDigits acc [] = acc
fromDigits acc (d:ds) =
  fromDigits ((ten `smul `acc) `add1` fromDigit zero d) ds

fromDigit acc [] = acc
fromDigit acc (b:bs) =
  fromDigit ((two `smul` acc) `add1` (if b then one else zero)) bs
