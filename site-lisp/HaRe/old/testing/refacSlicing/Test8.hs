module Test8 where

f l = l + (let x = 56;
               y = 67 in (let x = 56 in x + y))
