module Case4 where

data T = C1 Int Int | C2 Int

g (C1 x y) = 56

caseIt x = case x of 
            42 -> 1 + f (C1 1 2)
                    where
                     f (C1 x y) = x + y
                     f x = g (C1 1 2)
