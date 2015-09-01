module GuardsCase1 where


f x  = case x of
         1 -> g x
               where 
                 g x = x + 1
         _ -> 42