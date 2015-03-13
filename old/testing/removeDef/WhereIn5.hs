module WhereIn5 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove defintion 'foo' will fail.

(fac,fib,foo)=(5,8,10)

main :: Int
main = fac+ fib
