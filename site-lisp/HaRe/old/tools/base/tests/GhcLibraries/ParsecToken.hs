-- Dummy ParsecToken module
module ParsecToken where

import ParsecChar

data LanguageDef st
    = LanguageDef 
    { commentStart   :: String
    , commentEnd     :: String
    , commentLine    :: String
    , nestedComments :: Bool                  
    , identStart     :: CharParser st Char
    , identLetter    :: CharParser st Char
    , opStart        :: CharParser st Char
    , opLetter       :: CharParser st Char
    , reservedNames  :: [String]
    , reservedOpNames:: [String]
    , caseSensitive  :: Bool
    }                           
           
data TokenParser st
    = TokenParser{ identifier       :: CharParser st String
                 , reserved         :: String -> CharParser st ()
                 , operator         :: CharParser st String
                 , reservedOp       :: String -> CharParser st ()
                        
                 , charLiteral      :: CharParser st Char
                 , stringLiteral    :: CharParser st String
                 , natural          :: CharParser st Integer
                 , integer          :: CharParser st Integer
                 , float            :: CharParser st Double
                 , naturalOrFloat   :: CharParser st (Either Integer Double)
                 , decimal          :: CharParser st Integer
                 , hexadecimal      :: CharParser st Integer
                 , octal            :: CharParser st Integer
            
                 , symbol           :: String -> CharParser st String

                 , whiteSpace       :: CharParser st ()     
             

                 , semi             :: CharParser st String
                 , comma            :: CharParser st String
                 , colon            :: CharParser st String
                 , dot              :: CharParser st String
                 }

makeTokenParser :: LanguageDef st -> TokenParser st
makeTokenParser = undefined

lexeme           :: TokenParser st -> CharParser st a -> CharParser st a
lexeme = undefined
semiSep          :: TokenParser st -> CharParser st a -> CharParser st [a]
semiSep = undefined
semiSep1         :: TokenParser st -> CharParser st a -> CharParser st [a]
semiSep1 = undefined
commaSep         :: TokenParser st -> CharParser st a -> CharParser st [a]
commaSep = undefined
commaSep1        :: TokenParser st -> CharParser st a -> CharParser st [a]
commaSep1 = undefined
parens           :: TokenParser st -> CharParser st a -> CharParser st a 
parens = undefined
braces           :: TokenParser st -> CharParser st a -> CharParser st a
braces = undefined
angles           :: TokenParser st -> CharParser st a -> CharParser st a
angles = undefined
brackets         :: TokenParser st -> CharParser st a -> CharParser st a
brackets = undefined
squares          :: TokenParser st -> CharParser st a -> CharParser st a 
squares = undefined
