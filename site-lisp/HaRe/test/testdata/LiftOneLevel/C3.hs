module LiftOneLevel.C3 where

import LiftOneLevel.D3(pow)

anotherFun (x:xs) = x^pow + anotherFun xs

anotherFun [] = 0

