module Lambda1 where


f = \x -> \y -> x + y + 1


g = f (fib 27) (fib 30)


fib 1 = 1
fib 0 = 1
fib n = fib (n-1) + fib (n-2)