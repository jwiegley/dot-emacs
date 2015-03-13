module D2 where

{-lift 'sq' to top level. In this refactoring, 'sq' will
  be hided in the import declaraion of module 'D2' in module 'C2'.-}
 
sumSquares (x:xs) = sq x + sumSquares xs
  where 
     sq x = x ^ pow
     pow =2 
 
sumSquares [] = 0

