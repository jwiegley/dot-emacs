module B where
-- Test for refactor of if to case

foo x = if (odd x) then "Odd" else "Even"

bob x y = x + y


foo' x = case (odd x) of
  True -> "Odd"
  False -> "Even"

main = do
  putStrLn $ show $ foo 5

mary = [1,2,3]

h = bob 1 2

