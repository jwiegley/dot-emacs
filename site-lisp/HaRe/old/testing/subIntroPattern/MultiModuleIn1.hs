module MultiModuleIn1 where



f :: [ Int ] -> Int
f (y : ys) = head ys + head (tail ys)