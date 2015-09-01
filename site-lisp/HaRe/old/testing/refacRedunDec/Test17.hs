module Test17 where

f x = (case x of
           10  -> y + x
             where
                 y = 10
                 f = 25
           _ -> x)  + x
           where
             r = 56
