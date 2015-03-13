module MonadIn2 where
f (a, b, c)
    =   do let (z, y) = (a, b)
           case (z, y) of
               (l, m) -> return (l, m)
 
f_1 (a, b, c)
    =   do let (z, y) = (a, b)
           case (z, y) of
               (l, m) -> return 0
 