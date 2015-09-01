module D1 where

{-demote 'sq' to 'sumSquares'. This refactoring
  affects module 'D1' and 'C1' -}

sumSquares (x:xs) = sq + sumSquares xs
  where
    sq  = x ^pow 
sumSquares [] = 0


pow = 2

main = sumSquares [1..4]

