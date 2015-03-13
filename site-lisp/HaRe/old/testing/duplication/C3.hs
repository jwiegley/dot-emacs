module C3 (module D, module C3) where 

import D3 as D 

anotherFun (x:xs) = sq x + anotherFun xs
 
anotherFun [] = 0
  
 

