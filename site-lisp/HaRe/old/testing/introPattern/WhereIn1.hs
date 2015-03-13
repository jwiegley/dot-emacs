module WhereIn1 where


data Tree = Empty 
          | Leaf Int 
          | Node Tree Tree



flattern :: Tree -> [Int]
flattern x = undefined

g y = f y
       where
         f :: Tree -> Tree
         f x = case x of
              _ -> x