module WhereIn2 where

{- Lifting the local function 'sq' will fail because of the
   necessity of renaming.
-}
sumSquares x y = sq x + sq y        
           where 
                 sq 0 = 0
                 sq z = z^pow  --There is a comment
                 pow=2


anotherFun 0 y = sq y

sq x = x^2
