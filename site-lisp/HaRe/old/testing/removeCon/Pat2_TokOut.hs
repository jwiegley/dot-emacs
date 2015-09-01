module Pat2 where


data P = S P deriving Show


zero :: P
zero = (error "Z no longer defined for P at line: 4")

two :: P
two = S ( S (error "Z no longer defined for P at line: 4"))
