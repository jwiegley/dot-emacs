module Test10 where

f p z = p + (let x = 56;
                 y = 67 in (\x -> x))
