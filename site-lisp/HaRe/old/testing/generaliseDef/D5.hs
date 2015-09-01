module D5(sumFun,f,y) where

{- generalise function 'f' on the sub-expression '(y+1)' with a new 
   parameter 'z'. This refactoring affects modules 'D5' and 'A5' -}

y=0

f x =x + ( y + 1)
 
sumFun xs = sum $ map f xs 
