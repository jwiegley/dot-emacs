-- Dummy ParsecCombinator module
module ParsecChar where

import Parsec
type CharParser st a    = GenParser Char st a

alphaNum :: CharParser st Char
alphaNum = undefined

char :: Char -> CharParser st Char
char = undefined

newline :: CharParser st Char
newline = undefined
