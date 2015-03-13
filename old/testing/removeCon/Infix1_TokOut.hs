module Infix1 where

data T1 = C2 Int Int

g = error
        "f (C1 1 2) no longer defined for T1 at line: 3" + error
                                                               "f (C1 2 3) no longer defined for T1 at line: 3"
     where
       {- f (C1 x y) = x + y -}