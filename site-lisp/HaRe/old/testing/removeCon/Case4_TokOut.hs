module Case4 where

data T = C2 Int

{- g (C1 x y) = 56 -}

caseIt x = case x of 
            42 -> 1 + f ((error "C1 no longer defined for T at line: 3") 1 2)
                    where
                     {- f (C1 x y) = x + y -}
                     f x = error "g (C1 1 2) no longer defined for T at line: 3"
