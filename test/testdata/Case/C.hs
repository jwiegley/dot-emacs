module C where
-- Test for refactor of if to case
-- The comments on the then and else legs should be preserved

foo x = if (odd x)
          then -- This is an odd result
            bob x 1
          else -- This is an even result
            bob x 2

bob x y = x + y

