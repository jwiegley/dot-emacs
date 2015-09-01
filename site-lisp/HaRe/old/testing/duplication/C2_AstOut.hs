module C2 where
import D2 hiding (anotherFun)
anotherFun ((x : xs)) = (sq x) + (anotherFun xs)
anotherFun [] = 0
 