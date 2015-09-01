module Test9 where

f x = x + (let x = 56;
               y = 67 in (let x = 56 in y))
