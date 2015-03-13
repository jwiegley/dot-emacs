module RecordIn4 where


data S = S1 { x :: Int } | S2 { x :: Int } deriving Show

{- map2 xs = map (\y -> y {x = 1}) xs -}

map2 xs = (case ((\ y -> y {x = 1}), xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map f xs))

