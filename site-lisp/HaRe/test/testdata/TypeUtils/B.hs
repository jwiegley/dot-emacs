module TypeUtils.B where
-- Test for refactor of if to case

import Data.List -- For testing module graph
import TypeUtils.C -- For testing module graph

foo x = if (odd x) then "Odd" else "Even"

bob x y = let foo x = x + 2 in (let foo x = x+1 in x + foo y)
    where
        foo x = x + 1


foo' x = case (odd x) of
  True -> "Odd"
  False -> "Even"

main :: IO ()
main = do
  putStrLn $ show $ (foo (5 + 42))

mary :: [Integer]
mary = [1,2,3]

h z = bob z 2

data D = A | B String | C

subdecl x = zz x
  where
    zz n = n + 1

