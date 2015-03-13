module A1 where


data Tree = Empty 
          | Leaf Int 
          | Node Tree Tree



flattern :: Tree -> [Int]
flattern x = undefined

f x = case x of
              _ -> x