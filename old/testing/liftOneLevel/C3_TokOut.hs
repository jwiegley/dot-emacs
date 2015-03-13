module C3  where 

import D3(pow)

anotherFun (x:xs) =  x^pow + anotherFun xs

anotherFun [] = 0

 

