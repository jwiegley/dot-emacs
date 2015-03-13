module HaskellChars where
import Char

{-+
This module collects the definitions from the Lexical Syntax in appendix B.3
of the (revised) Haskell 98 report that define sets of characters.
These sets are referred to in the rest of the lexical syntax,
which is given in module HaskellLexicalSyntax.
-}

{-+
ASCII characters are represented by themselves, while
non-ASCII characters are represented by the class they belong to.
-}
data HaskellChar
  = ASCII Char
  | UniWhite   -- any Unicode character defined as whitespace
  | UniSymbol  -- any Unicode symbol or punctuation
  | UniDigit   -- any Unicode numeric
  | UniLarge   -- any uppercase or titlecase Unicode letter
  | UniSmall   -- any Unicode lowercase letter
  deriving (Eq,Ord{-,Show-})

acs = map ASCII

-- Character classifications:
special   = acs "(),;[]`{}"
creturn   = acs "\r"
linefeed  = acs "\LF"
vertab    = acs "\VT"
formfeed  = acs "\FF"
space     = acs " \xa0"
tab       = acs "\t"
uniWhite  = [UniWhite]
cany      = graphic++space++tab
graphic   = small++large++symbol++digit++special++acs ":\"'"++latin1Print
small     = ascSmall++uniSmall++acs "_"
ascSmall  = acs ['a'..'z']
uniSmall  = [UniSmall] ++acs latin1Lower -- because of isSymbol workaround
large     = ascLarge++uniLarge
ascLarge  = acs ['A'..'Z']
uniLarge  = [UniLarge] ++acs latin1Upper -- because of isSymbol workaround
symbol    = ascSymbol++uniSymbol
ascSymbol = acs "!#$%&*+./<=>?@\\^|-~"
uniSymbol = [UniSymbol]++acs latin1Symbol -- !! GHC missing isSymbol workaround
digit     = ascDigit++uniDigit
ascDigit  = acs ['0'..'9']
uniDigit  = [UniDigit]
octit     = acs ['0'..'7']
hexit     = digit ++ acs ['A'..'F'] ++ acs ['a'..'f']

-- Some of these are actually UniSmall, UniLarge, UniSymbol, but since GHC's
-- isUpper etc doesn't recognize them, we include them here, as a partial
-- workaround.
latin1Print = acs ['\160'..'\255']
latin1Upper = "ÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÐÑÒÓÔÕÖØÙÚÛÜÝÞ"
latin1Lower = "ßàáâãäåæçèéêëìíîïðñòóôõöøùúûüýþÿ"
latin1Symbol = "¡¢£¤¥¦§¨©¬­®¯°±´¶·¸¿×÷"

----

instance Show HaskellChar where
  showsPrec d h =
    case h of
      ASCII c   -> showsPrec d c
      UniWhite  -> showString "UW"
      UniSymbol -> showString "US"
      UniDigit  -> showString "UD"
      UniLarge  -> showString "UU"
      UniSmall  -> showString "UL"

  showList s = showChar '"' . foldr ((.).shC) id s . showChar '"'
    where
      shC h =
	case h of
	  ASCII c   -> showString (init . tail $ show c)
	  UniWhite  -> showS "UW"
	  UniSymbol -> showS "US"
	  UniDigit  -> showS "UD"
	  UniLarge  -> showS "UU"
	  UniSmall  -> showS "UL"
        where showS s = showChar '"' . showString s . showChar '"'
