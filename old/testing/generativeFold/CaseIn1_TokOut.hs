module CaseIn4 where


data S = S1 { x :: Int } | S2 { x :: Int } deriving Show

{- map2 xs = map ( \ y -> (case y of 
                              S1 _ -> S1 1
                              S2 _ -> S2 1)) xs -}
map2 xs = (case ((\ y -> case y of 
                            S1 _ -> S1 1
                            S2 _ -> S2 1), xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map2 xs))

