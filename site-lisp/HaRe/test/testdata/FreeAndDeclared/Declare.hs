module FreeAndDeclared.Declare (module FreeAndDeclared.Declare) where

import qualified Data.Generics as G

toplevel :: Integer -> Integer
toplevel x = c * x
 
c,d :: Integer
c = 7
d = 9

-- Pattern bind
tup :: (Int, Int)
h :: Int
t :: Int
tup@(h,t) = head $ zip [1..10] [3..15]

data D = A | B String | C

-- Retrieve the String from a B
unD (B y) = y
-- But no others.

-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714
data F = G | (:|) String String

unF (a :| b) = (a,b)

-- Main routine
main = do
  a <- getChar
  putStrLn "foo"

mkT = "no clash with Data.Generics"

ff z = G.gshow z

