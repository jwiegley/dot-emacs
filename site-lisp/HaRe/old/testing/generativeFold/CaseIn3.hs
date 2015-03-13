module CaseIn3 where


data S = S1 { x :: Int } | S2 { x :: Int } deriving Show

{- map2 xs = map ( \ (y:ys) -> (case y of 
                              S1 _ -> S1 1
                              S2 z | z /= 1 -> S2 1
                                   | otherwise -> S2 2)) xs -}
map2 xs = (case ((\ g -> case g of 
                            S1 _ -> S1 1
                            S2 x | x /= 1 -> S2 1
                                 | otherwise -> S2 2), xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map f xs))

