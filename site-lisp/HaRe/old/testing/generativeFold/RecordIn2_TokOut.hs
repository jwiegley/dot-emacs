module RecordIn2 where


data S = S1 { x :: Int } | S2 { x :: Int } deriving Show

{- map2 xs = map (\y -> S1 {x = 1}) xs -}

map2 xs = (case ((\ y -> S1 {x = 1}), xs, 1) of
               (f, [], n) -> []
               (f, (x : xs), n) -> (f x) : (map2 xs))