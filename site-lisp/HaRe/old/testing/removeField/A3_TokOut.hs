module A3 where

data Data a = C1 a Char |
              C2 Int        |
	      C3 Float

f :: Data a
f = (C1 "hello"  'c')


g = case f of
     (C1 x  z)  -> 42
     (C1 x  z) -> 43
     _           -> 0

