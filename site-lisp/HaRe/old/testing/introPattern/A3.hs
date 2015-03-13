module A3 where


data Tree = Empty 
          | Leaf Int 
          | Node Tree Tree

data T = C1 Tree

g :: T -> T
g x = x


flattern :: Tree -> [Int]
flattern x = undefined

f :: Tree -> Tree -> Int
f x y = case x of
              _ -> 42