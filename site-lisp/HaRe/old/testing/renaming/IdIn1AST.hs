module IdIn1 where
x1 = 5
 
foo = x1 + 3
 
bar z
    = (x + y) + z
  where
      x = 7
      y = 3
 
main = (foo, bar x1, foo)
 