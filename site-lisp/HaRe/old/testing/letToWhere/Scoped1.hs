module Scoped1 where

f =  let g = e
      in
       let g = e2
       in g

oo x 
  = case x of
      x 
       | x == 2 -> let y = 42 in y + x
      _ -> 0 


e = 1 * (10 ^ 6)

e2 = 87 * 9


j = 
      ( let p = 23232

        in (jkj (+) p))
    where
      jkj (+) p = p + 929292
    

j2 x
  | x ==0 = let g = 45 in g
  | otherwise = let g = 78 in g


