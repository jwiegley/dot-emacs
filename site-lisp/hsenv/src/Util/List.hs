module Util.List (breakOn) where

breakOn :: Eq a => a -> [a] -> Maybe ([a], [a])
breakOn sep = aux []
  where aux _ [] = Nothing
        aux prevs (x:xs) | x == sep   = Just (reverse prevs, xs)
                         | otherwise = aux (x:prevs) xs
