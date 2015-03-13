{-+
Except for one equation, this module provides an implementation of the
function L from section 9.3 of the revised Haskell 98 Report.
The missing equation is the one that requires interaction with the parser.
This means that things like

     let x=1
     in x+x

will be correctly translated to

     let {x=1}
     in x+x

but things like

     let x=1 in x+x

that should be parsed as

     let { x=1 } in x+x

will *not* be treated correctly in this implementation.
-}

module L(l) where
import HsTokens(Token(..))
default(Int)

-- The equations for cases when <n> is the first token:
l ts0@((Indent n,(p,_)):ts) ms0@(m:ms) | m==n = semi p:l ts ms0
                                       | n<m  = vrbrace p:l ts0 ms
l ((Indent _,_):ts) ms = l ts ms
-- The equations for cases when {n} is the first token:
l ((Open n,(p,_)):ts) (m:ms) | n>m = vlbrace p:l ts (n:m:ms)
l ((Open n,(p,_)):ts) []     | n>0 = vlbrace p:l ts [n]
l ((Open n,(p,_)):ts) ms       = vlbrace p:vrbrace p:l ((Indent n,(p,"")):ts) ms
-- Equations for explicit braces:
l (t1@(Special,(_,"}")):ts) (0:ms) = t1:l ts ms
l (t1@(Special,(p,"}")):ts) ms     = layout_error p "unexpected }"++ts -- hmm
l (t1@(Special,(p,"{")):ts) ms     = t1:l ts (0:ms)
-- The equation for ordinary tokens:
l (t:ts) ms = t:l ts ms
-- Equations for end of file:
l [] [] = [{-eoftoken-}]
l [] (m:ms) = if m/=0
	      then vrbrace eof:l [] ms
	      else layout_error eof "missing } at eof"

-- There are the tokens inserted by the layout processor:
vlbrace p = (Layout,(p,"{"))
vrbrace p = (Layout,(p,"}"))
semi p = (Special,(p,";"))

--eoftoken = (GotEOF,(eof,""))
eof = (-1,-1) -- hmm

layout_error p msg = [(ErrorToken,(p,"{-"++msg++"-}"))] -- hmm
