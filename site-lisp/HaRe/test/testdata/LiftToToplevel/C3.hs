module LiftToToplevel.C3  where 

import LiftToToplevel.D3(pow)

anotherFun (x:xs) =  x^pow + anotherFun xs

anotherFun [] = 0

 

