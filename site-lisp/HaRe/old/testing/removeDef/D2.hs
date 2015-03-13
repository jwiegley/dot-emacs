module D2 where

{-Remove function 'sq' should fail, as 'sq' is used by module 'C2'. -}

sumSquares (x:xs) = x^pow + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

