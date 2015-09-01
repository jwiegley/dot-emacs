module Case1 where

data T = C1 Int Int | C2 Int

f (C1 x y) = 56

caseIt x = case x of 
            42 -> error $ "f (C1 1 2)"
                    where
                     f (C1 x y) = x + y
