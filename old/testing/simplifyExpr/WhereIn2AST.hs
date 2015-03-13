module WhereIn2 where
f   =   (case (x, y, z) of
             (1, y, z) -> y + z
             (x, y, z) -> z)
  where
      (x, y, z) = g 42
      g x = (1, 2, x)
 
f_1 =   (case (x, y, z) of
             (1, y, z) -> return 0
             (x, y, z) -> return 1)
  where
      (x, y, z) = g 42
      g x = (1, 2, x)
 