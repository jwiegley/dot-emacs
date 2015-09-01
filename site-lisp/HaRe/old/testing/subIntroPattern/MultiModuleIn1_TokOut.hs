module MultiModuleIn1 where



f :: [ Int ] -> Int
f ((y : ys@[])) = (head ys) + (head (tail ys))
f ((y : ys@(b_1 : b_2)))
    = (head ys) + (head (tail ys))
f ((y : ys)) = (head ys) + (head (tail ys))