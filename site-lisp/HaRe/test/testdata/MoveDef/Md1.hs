module MoveDef.Md1 where

toplevel :: Integer -> Integer
toplevel x = c * x
 
c,d :: Integer
c = 7
d = 9

-- Pattern bind
tup :: (Int, Int)
h :: Int
t :: Int
tup@(h,t) = head $ zip [1..10] [3..ff]
  where
    ff :: Int
    ff = 15

data D = A | B String | C

ff :: Int -> Int
ff y = y + zz
  where
    zz = 1

l z =
  let
    ll = 34
  in ll + z

dd q = do
  let ss = 5
  return (ss + q)

zz1 a = 1 + toplevel a

-- General Comment
-- |haddock comment
tlFunc :: Integer -> Integer
tlFunc x = c * x
-- Comment at end


