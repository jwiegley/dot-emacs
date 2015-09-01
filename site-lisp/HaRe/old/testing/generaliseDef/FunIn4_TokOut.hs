module FunIn4 where

--In this example, 'x+y' can not be generalised as 'x' is a local variable declared in 'f'

y=0

f x =x + y + 1

g = f 1 