module Test7 where

f x y = x + (let y = 56;
                 p = 45 in y + p)
