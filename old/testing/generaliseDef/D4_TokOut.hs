module D4 where

{- generalise function 'f' on the sub-expression '1' with a new  parameter 'z',
   This refactoring affects the modules 'D4' and 'A4'-}

y=0

f z x =x + ( y + z)
 
sumFun xs = sum $ map (f 1) xs 