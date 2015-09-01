module GuardsCase2 where


f x  = case x of
         1  
          | x `mod` 4 == 0 -> g x
               where 
                 g x = x + 1
         _ -> 42