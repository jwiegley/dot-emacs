module MultiEquationIn1 where


f :: Either a b -> Maybe a -> a
f (Left a) Nothing = a
f (Left a) x = a