module A2 where


data Tree = Empty 
          | Leaf Int 
          | Node Tree Tree



flattern :: Tree -> [Int]
flattern x = undefined

f x = case x of
              _ -> x