module LiftOneLevel.C2 (module LiftOneLevel.D2, module LiftOneLevel.C2) where

import LiftOneLevel.D2

anotherFun (x:xs) = x^4 + anotherFun xs

anotherFun [] = 0

