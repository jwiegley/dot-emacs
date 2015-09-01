module Demote.D1 where

{-demote 'sq' to 'sumSquares'. This refactoring
  affects module 'D1' and 'C1' -}

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

