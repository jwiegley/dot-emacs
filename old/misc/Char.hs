module Char(
    isAscii, isLatin1, isControl, isPrint, isSpace, isUpper, isLower, 
    isAlpha, isDigit, isOctDigit, isHexDigit, isAlphaNum, 
    digitToInt, intToDigit,
    toUpper, toLower,
    ord, chr,
    readLitChar, showLitChar, lexLitChar,
    Char,String
 )
where
import Prelude
import PreludeBuiltin
import Numeric(readDec, readOct, lexDigits, readHex)
import Array
import Ix

isAscii, isControl, isPrint, isSpace            :: Char -> Bool
isUpper, isLower, isAlpha, isDigit, isAlphanum  :: Char -> Bool

isAscii c     =  c < '\x80'

isLatin1 c = c <= '\xff'

isControl c   =  c < ' ' || c >= '\DEL' && c <= '\x9f'

isPrint c     =  c >= ' '   &&  c <= '~' || c >= '\xa0'

isSpace c     =  c == ' '   || c == '\t'  || c == '\n'  || c == '\r'  ||
                               c == '\f'  || c == '\v' || c=='\xa0'

isUpper c     =
        c >= 'A' && c <= 'Z' 

isLower c     =
        c >= 'a' && c <= 'z'

isAlpha c     =  isUpper c  ||  isLower c
isDigit c     =  c >= '0'   &&  c <= '9'
isAlphanum c  =  isAlpha c  ||  isDigit c
isAlphaNum = isAlphanum

toUpper, toLower      :: Char -> Char

toUpper c | isLower c  = chr (ord c - ord 'a' + ord 'A')
          | otherwise  = c

toLower c | isUpper c  = chr (ord c - ord 'A' + ord 'a')
          | otherwise  = c

minChar, maxChar      :: Char
minChar                = chr 0
maxChar                = chr 255


isOctDigit c             =  c >= '0' && c <= '7'

isHexDigit c             =  isDigit c || c >= 'A' && c <= 'F' ||
                                         c >= 'a' && c <= 'f'
-- Digit conversion operations
digitToInt :: Char -> Int
digitToInt c
  | isDigit c            =  fromEnum c - fromEnum '0'
  | c >= 'a' && c <= 'f' =  fromEnum c - fromEnum 'a' + 10
  | c >= 'A' && c <= 'F' =  fromEnum c - fromEnum 'A' + 10
  | otherwise            =  error "Char.digitToInt: not a digit"

intToDigit :: Int -> Char
intToDigit i
  | i >= 0  && i <=  9   =  toEnum (fromEnum '0' + i)
  | i >= 10 && i <= 15   =  toEnum (fromEnum 'a' + i - 10)
  | otherwise            =  error "Char.intToDigit: not a digit"

ord c = primCharToInt c
chr n = primIntToChar n


-- Text functions
--readLitChar             :: ReadS Char
readLitChar ('\\':s)    =  readEsc s
        where
        readEsc ('a':s)  = [('\a',s)]
        readEsc ('b':s)  = [('\b',s)]
        readEsc ('f':s)  = [('\f',s)]
        readEsc ('n':s)  = [('\n',s)]
        readEsc ('r':s)  = [('\r',s)]
        readEsc ('t':s)  = [('\t',s)]
        readEsc ('v':s)  = [('\v',s)]
        readEsc ('\\':s) = [('\\',s)]
        readEsc ('"':s)  = [('"',s)]
        readEsc ('\'':s) = [('\'',s)]
        readEsc ('^':c:s) | c >= '@' && c <= '_'
                         = [(chr (ord c - ord '@'), s)]
        readEsc s@(d:_) | isDigit d
                         = [(chr n, t) | (n,t) <- readDec s]
        readEsc ('o':s)  = [(chr n, t) | (n,t) <- readOct s]
        readEsc ('x':s)  = [(chr n, t) | (n,t) <- readHex s]
        readEsc s@(c:_) | isUpper c
                         = let table = ('\DEL', "DEL") : assocs asciiTab
                           in case [(c,s') | (c, mne) <- table,
                                             ([],s') <- [match mne s]]
                              of (pr:_) -> [pr]
                                 []     -> []
        readEsc _        = []

	match                         :: (Eq a) => [a] -> [a] -> ([a],[a])
	match (x:xs) (y:ys) | x == y  =  match xs ys
	match xs     ys               =  (xs,ys)

readLitChar (c:s)       =  [(c,s)]
--}
showLitChar               :: Char -> ShowS
showLitChar c | c > '\DEL' =  showChar '\\' . 
                              protectEsc isDigit (shows (ord c))
showLitChar '\DEL'         =  showString "\\DEL"
showLitChar '\\'           =  showString "\\\\"
showLitChar c | c >= ' '   =  showChar c
showLitChar '\a'           =  showString "\\a"
showLitChar '\b'           =  showString "\\b"
showLitChar '\f'           =  showString "\\f"
showLitChar '\n'           =  showString "\\n"
showLitChar '\r'           =  showString "\\r"
showLitChar '\t'           =  showString "\\t"
showLitChar '\v'           =  showString "\\v"
showLitChar '\SO'          =  protectEsc (== 'H') (showString "\\SO")
showLitChar c              =  showString ('\\' : asciiTab!c)

protectEsc p f             = f . cont
                             where cont s@(c:_) | p c = "\\&" ++ s
                                   cont s             = s
asciiTab = listArray ('\NUL', ' ')
           ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
            "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI", 
            "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
            "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US", 
            "SP"] 

--lexLitChar          :: ReadS String
lexLitChar ('\\':s) =  [('\\':esc, t) | (esc,t) <- lexEsc s]
        where
          lexEsc (c:s)     | c `elem` "abfnrtv\\\"'" = [([c],s)]
          lexEsc s@(d:_)   | isDigit d               = lexDigits s
          lexEsc ('^':c:s) | c >= '@' && c <= '_'    = [(['^',c],s)]
          -- Very crude approximation to \XYZ.  Let readers work this out.
          lexEsc s@(c:_)   | isUpper c               = [span isCharName s]
          lexEsc _                                   = []
          isCharName c = isUpper c || isDigit c

lexLitChar (c:s)    =  [([c],s)]
lexLitChar ""       =  []
