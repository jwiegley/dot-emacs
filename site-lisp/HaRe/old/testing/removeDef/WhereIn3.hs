module WhereIn3 where


--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'fac'
fac :: Int -> Int
fac 0 = 1
fac 1 = 1
fac n = n * fac (n-1)
