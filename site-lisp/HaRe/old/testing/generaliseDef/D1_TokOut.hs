module D1(sumFun) where

{- generalise function 'f' on the sub-expression '(y+1)' with a new 
   parameter 'z'. This refactoring only affects the current module-}

y=0

f z x =x + z
 
sumFun xs = sum $ map (f (y + 1)) xs 
