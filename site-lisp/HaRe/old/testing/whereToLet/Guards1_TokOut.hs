module Guards1 where

f x
    =   let g x = 90 - x
        in if x == 1 then g (x + 1) else g x
     
