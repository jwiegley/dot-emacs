module WhereIn8 where

--lift 'b=17' one level up.
g y = f + 345
  where
      f = y + b
        where 
          b=17
   