module IdIn2 where
x = 5
 
foo = x + 3
 
bar z
    = (x1 + y) + z
  where
      x1 = 7
      y = 3
 
main = (foo, bar x, foo)
 