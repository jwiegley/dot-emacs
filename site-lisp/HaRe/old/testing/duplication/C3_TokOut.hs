module C3 (module D, module C3) where 

import D3 as D hiding (anotherFun) 

anotherFun (x:xs) = sq x + anotherFun xs
 
anotherFun [] = 0
  
 

