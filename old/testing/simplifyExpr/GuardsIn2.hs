module GuardsIn2 where

f x@1 y@(g:gs)
  | x == 1 = case y of 
               [] -> error "Error!"
               (l:ls) -> ls
  | otherwise = gs



g x@(y:ys) = case x of
              [] -> error "Error!"
              (x:xs) -> x



p x@(y:ys) = case x of
              [] -> error "Error!"
              (x:xs) -> x



