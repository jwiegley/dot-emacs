module LetIn3 where
sumSquares x y
    =   let pow = 2
             
            sq 0 = 0
            sq z = z ^ pow
        in (let in (sq x) + (sq y))
 
anotherFun 0 y = sq y where sq x = x ^ 2
 