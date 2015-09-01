module A1 where

format :: [a] -> [[a]] -> [[a]]
format sep xs
  = if len xs < 2 
      then xs
      else (head xs ++ sep) : format sep (tail xs)

{- fmt = format "\n" -}

fmt = (\ xs ->
           if (len xs) < 2
           then xs
           else ((head xs) ++ "\n") : (fmt (tail xs)))



len x = length x

{- map2 xs = map len xs -}

map2 xs = (case (len, xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map f xs))


fac45 = fac 45



fac 1 = 1
fac n = n * fac (n-1)
