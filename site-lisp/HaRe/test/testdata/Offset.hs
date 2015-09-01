module Offset where

-- Test getOffset in various indented cases

bob a b = x
  where x = 3

bib a b = x
  where 
    x = 3


bab a b =
  let bar = 3
  in     b + bar

foo x y =
  do c <- getChar
     return c

fud a b = let bar = 3
          in b + bar




