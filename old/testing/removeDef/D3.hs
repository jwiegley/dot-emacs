module D3 where

{-Remove function 'sq' should successs, as it is used by neither the
  current module nor the client modules
-}

sumSquares (x:xs) = x^pow + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

