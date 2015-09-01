module Mixfix where
import List (intersperse)

mixfix' :: String -> [ShowS] -> ShowS
mixfix' ('_':cs) (p:ps) = p . mixfix' cs ps
mixfix' ('\\':c:cs) ps = showChar c . mixfix' cs ps
mixfix' (c:cs) ps = showChar c . mixfix' cs ps
mixfix' _ _ = id

mixfix :: String -> [ShowS] -> Int -> Int -> ShowS
mixfix cs ps p0 p = showParen (p > p0) (mixfix' cs ps)

showSpace = showChar ' '
showLR l r x = showString l . x . showString r
showQuotes = showLR "\"" "\""
showBraces = showLR "{" "}"
showParens = showLR "(" ")"
showAngles = showLR "<" ">"
showSquares = showLR "[" "]"

showAll xs = foldr (.) id xs
showSep sep xs = showAll (intersperse sep xs)
showCommaSep = showSep (showChar ',')
showSpaceSep = showSep showSpace
showBarSep = showSep (showString " | ")

showTuple xs = showParens (showCommaSep xs)
