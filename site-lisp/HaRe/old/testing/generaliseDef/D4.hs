module D4 where

{- generalise function 'f' on the sub-expression '1' with a new  parameter 'z',
   This refactoring affects the modules 'D4' and 'A4'-}

y=0

f x =x + ( y + 1)
 
sumFun xs = sum $ map f xs 