module WhereIn2 where


f = (y + z)
        where
          (x,y,z) = g 42
          g x = (1,2,x)


