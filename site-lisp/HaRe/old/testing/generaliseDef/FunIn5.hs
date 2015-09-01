module FunIn5 where

--In this example, 'y+1' in function 'f' can not be generalised as 'x', as this
--would cause name clash.

y=0

f x =x + (y + 1)

g = f 1 