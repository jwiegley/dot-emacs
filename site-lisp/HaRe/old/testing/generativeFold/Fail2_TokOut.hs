
module Fail2 where

deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]   

deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys  