module D2 where

{-lift 'sq' to top level. In this refactoring, 'sq' will
  be hided in the import declaraion of module 'D2' in module 'C2'.-}
 
sumSquares (x:xs) = (sq pow) x + sumSquares xs
  where 
     pow =2 
 
sumSquares [] = 0

sq pow x = x ^ pow


