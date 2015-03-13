module D1(sumFun) where

{- generalise function 'f' on the sub-expression '(y+1)' with a new 
   parameter 'z'. This refactoring only affects the current module-}

y=0

f x =x + ( y + 1)
 
sumFun xs = sum $ map f xs 
