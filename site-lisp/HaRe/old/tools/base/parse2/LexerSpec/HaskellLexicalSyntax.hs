module HaskellLexicalSyntax where
{-+
This module is a transcription of the Lexical Syntax given in appendix B.2
of the Haskell 98 Report, except for character set definitions, which are
given in module HaskellChars.

The grammar below contains extra annotations (not found in the report) to
allow the recognized strings to be paired with token classifications, which
are used in the token specifications in the Happy parser.
-}
import List((\\))
import HaskellChars
import HsTokens
import RegExp

--
program = many (lexeme ! whitespace)

lexeme  = varid      & o Varid  
        ! conid      & o Conid
        ! varsym     & o Varsym
        ! consym     & o Consym
        ! literal -- & o Literal
        ! a special  & o Special
        ! reservedop & o Reservedop
        ! reservedid & o Reservedid
--      ! specialid  & o Specialid -- recognized by the parser

        ! qvarid     & o Qvarid
        ! qconid     & o Qconid
        ! qvarsym    & o Qvarsym
        ! qconsym    & o Qconsym

literal = integer    & o IntLit
        ! float      & o FloatLit
        ! char       & o CharLit
        ! string     & o StringLit

whitechar = newline ! a vertab ! a space ! a tab ! a uniWhite
newline   = a creturn & a linefeed
          ! a creturn ! a linefeed ! a formfeed

whitespace = some whitechar & o Whitespace
           ! comment & o Comment
           ! ncomment & o NestedComment
comment = dashes & o Commentstart & many (a cany) & newline
dashes = as "--" & many (aa "-")
opencom = as "{-"
--closecom = as "-}"
ncomment = opencom & o NestedCommentStart -- handled by calling an external function

-- This doesn't work, since regular expressions can't be recursive...
--ncomment = opencom & lANYseq & many (ncomment & lANYseq) & closecom
--ncomment = fix (opencom & lANYseq & many (Self & lANYseq) & closecom)

--ncomment = opencom & lANYseq & closecom -- unnested comments!
--lANYseq = many cANY -! (many cANY & ( opencom ! closecom ) & many cANY)
--cANY      = a graphic ! whitechar


varid = a small & idtail -! reservedid
conid = a large & idtail
idtail = many (a small ! a large ! a digit ! aa "'")

reservedid =
  ass [ "case", "class", "data", "default", "deriving", "do", "else",
        "if", "import", "in", "infix", "infixl", "infixr", "instance",
        "let", "module", "newtype", "of", "then", "type", "where", "_"]

{-
specialid = as"as" ! as"qualified" ! as"hiding" 
          ! as"forall" -- rank 2 polymorphism extension
          ! as"primitive" -- Hugs foreign function interface
-}

varsym = (a symbol & many (a symbol ! aa ":")) -! (reservedop ! dashes)
consym = (aa ":" & many (a symbol ! aa ":")) -! reservedop

reservedop = ass ["..", ":","::", "=","\\","|","<-","->","@","~","=>"]

--specialop = aa "-" ! aa "!" -- recognized by the parser instead

modid = conid
--optq = opt qual

-- qual = modid & aa "." -- For Haskell 98
qual = some (modid & aa ".") -- For "hierachical module names"

{-+
In the report, qvarid etc include both qualified and unqualified names, but
here they denote qualified names only. This allows qualified and unqualified
names to be distinguished in a more natural way in the parser.
-}
qvarid = qual & varid
qconid = qual & conid
qvarsym = qual & varsym
qconsym = qual & consym

decimal = some (a digit)
octal = some (a octit)
hexadecimal = some (a hexit)

integer = decimal
        ! aa "0" & aa "Oo" & octal
	! aa "0" & aa "Xx" & hexadecimal

float = decimal & aa "." & decimal & opt (aa "eE" & opt (aa "-+") & decimal)
char = aa "'" & (a (graphic \\ acs "'\\") ! a space ! escape{-<\&>-}) & aa "'"
string = aa "\"" & many (a (graphic \\ acs "\"\\") ! a space ! escape ! gap) & aa "\""

escape = aa "\\" & ( charesc ! ascii ! decimal !
                    aa "o" & octal ! aa "x" & hexadecimal )

charesc = aa "abfnrtv\\\"'&"

ascii = aa "^" & cntrl !
        ass [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK",
     "BEL", "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI", "DLE",
     "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB", "CAN",
     "EM", "SUB", "ESC", "FS", "GS", "RS", "US", "SP", "DEL"]

cntrl = a ascLarge ! aa "@[\\]^_"

gap = aa "\\" & some whitechar & aa "\\"

--
aa = a . acs -- any of the ASCII chars
as = ts . acs -- ASCII string
ass = foldr1 (!) . map as

--
--tyvar = varid
--tycon = conid
--tycls = conid
--qtycon = qual & tycon
--qtycls = qual & tycls
