module C2 (module D2, module C2) where
import D2 hiding (sq)
anotherFun ((x : xs)) = (x ^ 4) + (anotherFun xs)
anotherFun [] = 0
 