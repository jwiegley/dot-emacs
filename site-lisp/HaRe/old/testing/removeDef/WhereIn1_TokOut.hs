module WhereIn1 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove defintion 'main'

fac,fib :: Int -> Int
fac 0 = 1
fac 1 = 1
fac n = n * fac (n-1)

fib 0 = 1
fib 1 = 1
fib n = (fib (n-1)) + (fib (n-2))


--This comment will not be removed.
