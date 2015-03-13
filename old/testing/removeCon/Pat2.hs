module Pat2 where


data P = Z | S P deriving Show


zero :: P
zero = Z

two :: P
two = S ( S Z)
