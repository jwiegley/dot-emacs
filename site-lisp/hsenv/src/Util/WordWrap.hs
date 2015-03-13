module Util.WordWrap (wordWrap) where

import Data.Char (isSpace)

trim :: String -> String
trim = trimAndReverse . trimAndReverse
  where trimAndReverse = reverse . dropWhile isSpace

reverseBreak :: (a -> Bool) -> [a] -> ([a], [a])
reverseBreak f xs = (reverse before, reverse after)
  where (after, before) = break f $ reverse xs

wordWrap :: Int -> String -> [String]
wordWrap maxLen line =
    case break (== '\n') chunk of
      (beginning, '\n':rest) -> beginning : wordWrap maxLen (rest ++ chunks)
      _ -> wordWrap' maxLen line
    where (chunk, chunks) = splitAt maxLen line

wordWrap' :: Int -> String -> [String]
wordWrap' maxLen line
  | length line <= maxLen = [trim line]
  | any isSpace beforeMax = trim beforeSpace : wordWrap maxLen (afterSpace ++ afterMax)
  | otherwise = firstBigWord : wordWrap maxLen rest
    where (beforeMax, afterMax) = splitAt maxLen line
          (beforeSpace, afterSpace) = reverseBreak isSpace beforeMax
          (firstBigWord, rest) = break isSpace line
