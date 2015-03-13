module ParsedSyntax(module Syntax,Src,lexerPass0) where
import Syntax

type Src i = i

lexerPass0 :: String -> () -- to avoid ambiguous overloading
lexerPass0 =
  error "This function is only available with the new parser and lexer."
