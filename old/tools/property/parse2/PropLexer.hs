module PropLexer(module PropLexer{-,LexerFlags(..)-}) where
--import LexerOptions
import HsLexerPass1(lexerPass0,lexerPass0',startPos)
import HsTokens

{-+
This module defines the lexical analyser for the P-logic extension of Haskell.

Differences from the plain Haskell 98 lexical syntax:

  - The identifiers "assert" and "property" are reserved.
  - The contents of nested comments of the form {-P: ... -} are parsed as
    normal code, providing a convenient way to hide assertions and predicate
    declarations from standard Haskell impementations.
-}

pLexerPass0 plogic =
    if plogic
    then propLexerPass0
    else lexerPass0
  where
    propLexerPass0 = propLexerPass0' startPos
    propLexerPass0' pos = concatMap plogicTokens . lexerPass0' pos

    plogicTokens t@(Varid,ps@(_,s)) =
      case s of
	"assert"   -> [(Reservedid,ps)]
	"property" -> [(Reservedid,ps)]
	_          -> [t]
    plogicTokens t@(NestedComment,ps@(p,'{':'-':'P':':':s)) =
        propLexerPass0' p (adjust s)
    plogicTokens t = [t]

    -- Replace the delimiting "{-P:" and "-}" with the same amount of space
    -- to preserve layout.
    adjust s = "    "++reverse ("  "++drop 2 (reverse s))
