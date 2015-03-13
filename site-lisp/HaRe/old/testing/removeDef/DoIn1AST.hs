module DoIn1 where
io s
    =   do s <- getLine
           let q = (s ++ s)
           putStr q
           putStr "foo"
 