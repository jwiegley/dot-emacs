module RecordIn6 where


data S = S1 { x :: Int } | S2 { x :: Int } deriving Show

{- map2 xs = map (\y -> y {x = 1}) xs -}

map2 xs = (case ((\ y -> y {x = 1}), xs,42) of
               (f, [], n) -> []
               (f, (x : xs),n) -> (f x) : (map (\ y -> y {x = n}) xs))

