module RecursionIn1 where

--A top level definition can be duplicated.

--In this example: duplicate the definition 'fac' with new name 'anotherFac'
--Pay attention to the recursion.

fac :: Int -> Int
fac 0 = 1
fac 1 = 1
fac n = n * fac (n-1)

anotherFac :: Int -> Int
anotherFac 0 = 1
anotherFac 1 = 1
anotherFac n = n * anotherFac (n-1)

fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = (fib (n-1)) + (fib (n-2))

main :: Int
main = fac 5 + fib 3
