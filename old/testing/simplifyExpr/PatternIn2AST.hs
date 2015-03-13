module PatternIn2 where
f ((z : zs))
    =   let y = (z : zs)
        in case y of
               [] -> error "Error: empty list!"
               (x : xs) -> x
 
f_1 ((z : zs))
    =   let y = (z : zs)
        in case y of
               [] -> return 0
               (x : xs) -> return 1
 