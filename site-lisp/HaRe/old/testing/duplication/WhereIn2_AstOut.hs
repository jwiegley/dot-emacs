module WhereIn2 where
x = 5
 
foo,bar :: Int -> Int
 
foo x = x + 3
 
anotherFoo :: Int -> Int
 
anotherFoo x = x + 3
 
bar z
    = (x + y) + z
  where
      x = 7
      y = 3
 
ram = (let fred = (let x = 5 in x) in fred + x) + 1
 
main = (foo 1, bar x, ram)
 