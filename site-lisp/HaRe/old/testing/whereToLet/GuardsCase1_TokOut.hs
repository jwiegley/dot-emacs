module GuardsCase1 where


f x  = case x of
         1 -> let g x = x + 1 in g x
               
         _ -> 42