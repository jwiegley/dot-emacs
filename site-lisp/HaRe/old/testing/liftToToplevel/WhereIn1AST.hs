module WhereIn1 where
sumSquares x y
    = ((sq pow) x) + ((sq pow) y) where pow = 2
 
sq 0 = 0
sq z = z ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 