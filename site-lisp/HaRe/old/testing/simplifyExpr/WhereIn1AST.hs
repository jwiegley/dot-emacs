module WhereIn1 where
f   =   (case (x, z) of
             (1, 2) -> "First Branch"
             _ -> "Second Branch")
  where (x, z) = (1, 2)
 
f_1 =   (case (x, z) of
             (1, 2) -> return 0
             _ -> return 1)
  where (x, z) = (1, 2)
 