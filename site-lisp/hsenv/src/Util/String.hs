module Util.String (padTo) where

padTo :: String -> Int -> String
padTo s n | length s < n = take n $ s ++ repeat ' '
          | otherwise    = s
