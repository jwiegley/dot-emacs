module WhereIn3 where
x = 5
 
foo,bar :: Int -> Int
 
foo x = x + 3
 
bar z
    = (x + y) + z
  where
      x,y :: Int
      x = 7
      xs :: Int
      xs = 7
      y = 3
 
ram = (let fred = (let x = 5 in x) in fred + x) + 1
 
main = (foo 1, bar x, ram)
 