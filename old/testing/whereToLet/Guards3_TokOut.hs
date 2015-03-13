module Guards3 where

f
    =   let g :: Int -> Int
             
            g 1 = 45
            g x = 90 - x
        in if x == 1 then g (x + 1) else g x
     where
       

       x = 56
