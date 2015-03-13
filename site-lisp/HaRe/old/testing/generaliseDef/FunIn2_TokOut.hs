module FunIn2 where

--In this example, the sub-expression '(y+1)' in function 'f' is generalised as parameter 'z'
--This example aims to test renaming identifiers.

y=0

f x =x + ( y + 1)

g = f 1 + y
   where y=1