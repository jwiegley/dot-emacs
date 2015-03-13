module WhereIn3 where
sumSquares x y
    = (sq_1 pow x) + (sq_1 pow y) where pow = 2
 
sq_1 pow 0 = 0
sq_1 pow z = z ^ pow
 
anotherFun 0 y = sq y
 
sq x = x ^ 2
 