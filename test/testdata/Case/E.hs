module E where
-- Test for refactor of if to case in a complex sub level
-- The comments on the then and else legs should be preserved

foo x = bob x f
  where
    f = (if (odd x)
          then do
            -- This is an odd result
            bob x 1
          else do
            -- This is an even result
            bob x 2) + 2

bob x y = x + y

