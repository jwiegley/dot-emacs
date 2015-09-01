module WhereIn4 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove defintion 'fac' will fail.

fac=5

fib=8

main :: Int
main = fac+ fib
