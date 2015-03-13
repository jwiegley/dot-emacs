
module Fail1 where

{- no comment equation defined for the generative fold, ergo failure. -}

x = 42


deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]   

deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys  