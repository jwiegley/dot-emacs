module Tst1 where

data Bool = False | True

data Nat = Zero | Succ Nat

-- length :: [a] -> Nat
length []     = Zero
length (x:xs) = Succ (length xs)

-- map :: (a->b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x:map f xs

mapLengthProp f xs = length (map f xs) == length xs

---

Zero   == Zero   = True
Succ _ == Zero   = False
Zero   == Succ _ = False
Succ n == Succ m = n==m
