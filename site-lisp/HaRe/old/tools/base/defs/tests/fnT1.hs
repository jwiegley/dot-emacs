data S = S { x :: [Int]}

g z@(S {x = y:ys})  = x x x x

f (x:xs) = x:xs




