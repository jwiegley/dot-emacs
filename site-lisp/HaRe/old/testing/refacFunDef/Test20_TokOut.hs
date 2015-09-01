module Test20 where

y c = c

f n y = n y

g = (f (f 1) 1)
h = f (+1) 1

