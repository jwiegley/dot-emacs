module TypeUtils.S where
-- Test for refactor of if to case

foo x = if (odd x) then "Odd" else "Even"

data D = A | B String | C

subdecl x = zz x
  where
    zz n = n + 1

