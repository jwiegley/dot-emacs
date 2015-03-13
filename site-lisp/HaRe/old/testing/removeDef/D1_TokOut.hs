module D1(sumSquares, sq) where

{-Remove function 'sq' should fail, as 'sq' is explicitly exported. -}

sumSquares (x:xs) = x^pow + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

