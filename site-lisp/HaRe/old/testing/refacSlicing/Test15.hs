module Test15 where

f x =  case x of
            10  -> y + f
              where
                  y = 10
                  f = 25
            _ -> x


