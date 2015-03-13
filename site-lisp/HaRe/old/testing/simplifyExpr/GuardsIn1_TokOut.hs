module GuardsIn1 where

f x y@(g:gs)
  | x == 1 = gs
  | otherwise = gs


g x@(y:ys) = case x of
              [] -> error "Error!"
              (x:xs) -> x



p x@(y:ys) = case x of
              [] -> error "Error!"
              (x:xs) -> x



