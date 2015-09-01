-- This program generates the core of lexical analyser for Haskell

import HaskellLexicalSyntax(program) -- The lexical syntax specification
import LexerGen(lexerGen)            -- The lexer generator implementation
import System(getArgs)

main = putStrLn . lexerGen "HsLex" "haskellLex" program =<< getArgs
