module C3 (module D3, module C3) where 

import D3 

anotherFun (x:xs) = x^pow + anotherFun xs

anotherFun [] = 0



