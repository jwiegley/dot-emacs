module WhereIn1 where


f = (case (x,z) of
      (1,2) -> "First Branch"
      _     -> "Second Branch")
       where
        (x,z) = (1,2)