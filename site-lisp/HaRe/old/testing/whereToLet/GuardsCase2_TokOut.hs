module GuardsCase2 where


f x  = case x of
         1  
            ->  let g x = x + 1
                in if (x `mod` 4) == 0
                   then g x
                   else error "UnMatched Pattern"
               
         _ -> 42