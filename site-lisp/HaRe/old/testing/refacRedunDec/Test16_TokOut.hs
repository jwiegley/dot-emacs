module Test16 where

f x  = (case x of
            10  -> y + r
              where
                  y = 10
                  f = 25
            _ -> x)
  
  where
    r = 56
            