module LocalWhereIn2 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'square'

sumSquares  x y =sq x + sq y
           where  square :: Int->Int  {-The 'where' will be removed-}
                  square x= x^2   {- This comment will be removed -}

sq x= x^pow
    where pow=2   

anotherFun x =sumSquares x x       


