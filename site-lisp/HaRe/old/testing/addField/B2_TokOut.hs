module B2 where

data Data1 a = C1 a a Int Int |
               C2 Int        |
	       C3 Float


g = (C1 undefined 1 2 3)

f = do
       (C1 c1_1 x y z) <- return (C1 undefined 1 2 3)
       let bob = y + 42

       return bob


