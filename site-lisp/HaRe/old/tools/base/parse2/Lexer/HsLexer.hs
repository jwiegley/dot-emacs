module HsLexer where
import ParseMonad
import HsTokens(Token(..))
--import MUtils
--import IOExts(trace)

{-+
This module implements the part of the lexer that interacts with the
Happy parser, i.e., the layout processing.
-}

lexer cont = cont =<< token

{-+ #popContext#, together with the error handling in the Happy parser,
implements the equation dealing with parse-error(t) in the definition of
the function L, in secion 9.3 in the revised Haskell 98 report.
-}

popContext =  do (ts,m:ms) <- get
		 if m/=0 then set (ts,ms) -- redudant test
		  else fail "Grammar bug? Unbalanced implicit braces?"

token = uncurry l =<< get
  where
    -- Here is the rest of the function L in the report:
    -- The equations for cases when <n> is the first token:
    l ts0@((Indent n,(p,_)):ts) ms0@(m:ms)
	| m==n      = ok (semi p)    ts  ms0
	| n<m       = ok (vrcurly p) ts0 ms
    l ((Indent _,_):ts) ms = l ts ms
    -- The equations for cases when {n} is the first token:
    l ((Open n,(p,_)):ts) (m:ms) | n>m = ok (vlcurly p) ts (n:m:ms)
    l ((Open n,(p,_)):ts) []     | n>0 = ok (vlcurly p) ts [n]
    l ((Open n,(p,_)):ts) ms           = ok (vlcurly p) -- (1st of 2 tokens)
					    (vrcurly p:(Indent n,(p,"")):ts)
				            (0:ms)
    -- Equations for explicit braces:
    l (t1@(Special,(_,"}")):ts) (0:ms) = ok t1 ts ms
    l (t1@(Layout, (_,"}")):ts) (0:ms) = ok t1 ts ms -- (2nd of 2 tokens)
    -- Haskell 98 Report bug workaround:
    l ts0@(t1@(Special,(p,"}")):ts) (m:ms) = ok (vrcurly p) ts0 ms
    l (t1@(Special,(_,"}")):ts) ms     = fail "unexpected }"
      
    l (t1@(Special,(p,"{")):ts) ms     = ok t1 ts (0:ms)
    -- The equation for ordinary tokens:
    l (t:ts) ms = ok t ts ms
    -- Equations for end of file:
    l [] [] = return eoftoken
    l [] (m:ms) = if m/=0
		  then ok (vrcurly eof) [] ms
		  else fail "missing } at eof"

    ok t ts ctx =
      --trace (show (t,ctx)) $
      setreturn t (ts,ctx)

    vlcurly p = (Layout,(p,"{"))
    vrcurly p = (Layout,(p,"}"))
    semi p = (Special,(p,";"))
