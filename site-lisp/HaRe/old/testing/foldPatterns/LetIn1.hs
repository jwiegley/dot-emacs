module LetIn1 where


f = let g :: [Int] -> Int
        g x@[] = (hd x) + (hd (tl x))
        g x@(z : zs) = (hd x) + (hd (tl x))
        g x = (hd x) + (hd (tl x))
    in g [1,2,3,4,5]
     where
      hd x = head x
      tl x = tail x

