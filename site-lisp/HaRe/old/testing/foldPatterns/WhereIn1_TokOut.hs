module WhereIn1 where


f x y = hd y + hd (tl y) 
         where
          hd x = x
          tl y = tail y