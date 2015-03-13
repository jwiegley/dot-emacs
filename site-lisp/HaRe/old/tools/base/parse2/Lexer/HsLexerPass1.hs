module HsLexerPass1(module HsLexerPass1,module HsLexerPos) where
import HsLex(haskellLex)
import HsLexUtils
import HsLayoutPre(layoutPre,PosToken)
import HsLexerPos
import Data.List(mapAccumL)

default(Int)

{-+
The function #lexerPass1# handles the part of lexical analysis that
can be done independently of the parser, i.e., the tokenization and the
addition of the extra layout tokens &lt;n&gt; and {n}, as specified in
section 9.3 of the revised Haskell 98 Report.
-}

type LexerOutput = [PosToken]
type Lexer = String -> LexerOutput

lexerPass1 :: Lexer
lexerPass1 = lexerPass1Only . lexerPass0

lexerPass1Only = layoutPre . rmSpace

rmSpace = filter (notWhite.fst)

notWhite t = t/=Whitespace &&
             t/=Commentstart && t/=Comment &&
             t/=NestedComment

-- Tokenize and add position information:

lexerPass0 :: Lexer
lexerPass0 = lexerPass0' startPos

lexerPass0' :: Pos -> Lexer
lexerPass0' pos0 = addPos . haskellLex . rmcr
  where
    addPos = snd . mapAccumL pos pos0

    pos p (t,s) = {-seq p'-} (p',(t,(p,s)))
        where p' = nextPos p s
--      where s = reverse r

{-+
Since #nextPos# examines one character at a time, it will increase the line
number by 2 if it sees \CR\LF, which can happen when reading DOS files on
a Unix like system.
Since the extra \CR characters can cause trouble later as well, we choose
to simply remove them here.
-}
rmcr ('\CR':'\LF':s) = '\LF':rmcr s
rmcr (c:s) = c:rmcr s
rmcr "" = ""
