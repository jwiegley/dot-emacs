module HsLayoutPre(layoutPre,PosToken) where
import HsTokens
import HsLexerPos

{-+
This is
an implementation of Haskell layout, as specified in section 9.3 of the
revised Haskell 98 report.

This module contains the layout preprocessor that inserts the extra
&lt;n&gt; and {n} tokens.
-}

type PosToken = (Token,(Pos,String))

layoutPre :: [PosToken] -> [PosToken]
layoutPre = indent . open

open = open1

{-+
If the first lexeme of a module is not { or module, then it is preceded
by {n} where n is the indentation of the lexeme.
-}
open1 (t1@(Reservedid,(_,"module")):ts) = t1:open2 ts
open1 (t1@(Special,(_,"{")):ts)         = t1:open2 ts
open1 ts@((t,(p,s)):_)	                = (Open (column p),(p,"")):open2 ts
open1 []                                = []

{-+
If a let, where, do, or of keyword is not followed by the lexeme {,
the token {n} is inserted after the keyword, where n is the indentation of
the next lexeme if there is one, or 0 if the end of file has been reached.
-}
open2 (t1:ts1) | isLtoken t1 =
    case ts1 of
      t2@(_,(p,_)):ts2 ->
        if notLBrace t2
        then t1:(Open (column p),(p,"")):open2 ts1
	else t1:t2:open2 ts2
      [] -> t1:(Open 0,(fst (snd t1),"")):[]
  where
    isLtoken (Reservedid,(_,s)) = s `elem` ["let","where","do","of"]
    isLtoken _ = False

    notLBrace (Special,(_,"{")) = False
    notLBrace _ = True
open2 (t:ts) = t:open2 ts
open2 [] = []

{-+
(This is from the original Haskell 98 report.)
The first token on each line (not including tokens already annotated) is
preceeded by &lt;n&gt;, where n is the indentation of the token.
-}
indent (t1@(Open _,(p,_)):ts) = t1:indent2 (line p) ts
indent (t1@(t,(p,s)):ts)    = (Indent (column p),(p,"")):t1:indent2 (line p) ts
indent [] = []

indent2 r (t1@(_,(p,_)):ts) | line p==r = t1:indent2 r ts
indent2 r ts = indent ts
