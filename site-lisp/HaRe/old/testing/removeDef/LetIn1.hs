module LetIn1 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'square'

sumSquares  x y =let square x
                       = x^2 
                     sq x=x^pow
                         where pow=2
                 in  sq x + sq y

anotherFun x =sumSquares x x       


