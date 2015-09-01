module Oops where

-- highlight >x +< in f, then select IntroNewDef

main = print ((f 1) 2, gaga True)
  where f x y = g + y
          where
            g = x
        gaga h =  ("g: " ++) (show h)
