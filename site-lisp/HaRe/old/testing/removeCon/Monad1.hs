module Monad1 where

data T1 a b = C1 a b | C2 b a


f x = do
        let g (C1 x y) = x + y
        return (g (C1 x 2))

