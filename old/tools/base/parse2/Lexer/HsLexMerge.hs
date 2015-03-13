module HsLexMerge where
import HsLexerPos(Pos(..),startPos,nextPos,nextPos1)
import HsTokens
--import OpTypes(eqBy)
import Data.List(groupBy)
import Unlit(CommentClass(..))

{-+ #mergeLex#: Merge literate comments with a token stream
Note: this may split tokens, so the result is not suitable for parsing!!
-}
--mergeLex :: ([String], [PosToken]) -> [PosToken]
mergeLex ([],ts) = ts -- for efficiency when tokens are not from a literal file
mergeLex (litcmnts,ts) =
    rejoin .
    addSpace startPos .
    merge (groupLit (addPos litcmnts)) .
    concatMap split .
    filter notSpace
    $ ts
  where
    addPos = zipWith pos [1..]
       where pos l s = (Pos 0 l 1,s) -- dummy character position

    notSpace (t,_) = t/=Whitespace

    split (t,(Pos n y x,s)) =
	[(t,(Pos n y' x',l))|((y',x'),l)<-zip ps (lines s),l/=""]
      where ps = zip [y..] (x:repeat 1)

    rejoin [] = []
    rejoin (t@(tt,(p@Pos{char=n},s)):ts) =
      case rejoin ts of
        t'@(tt',(Pos{char=n'},s')):ts' | n>0 && tt==tt' && n'==n -> (tt,(p,s++s')):ts'
	ts' -> t:ts'

    groupLit = map join . groupBy bothLitCmnt
      where
        bothLitCmnt (_,(LitCmnt,_)) (_,(LitCmnt,_)) = True
	bothLitCmnt _ _ = False

        join ((p,(LitCmnt,s)):cs) = (p,(LitCmnt,unlines (s:map (snd.snd) cs)))
        join [l] = l

    litc (p,(cc,c)) = (conv cc,(p,c))
      where
        conv LitCmnt = LiterateComment
	conv _       = Whitespace

    merge [] ts = ts
    merge cmnts [] = map litc cmnts

    merge cs0@(c@(pc,sc):cs) ts0@(t@(tt,(pt,s)):ts) =
	if pc<=pt
	then litc c:merge cs ts0
	else --if pt'<=pc then
	       t:merge cs0 ts
	     --else error "literate comment inside token not handled yet"
        -- TODO: handle tokens containing literate comments
{-
      where
        pc' = nextPos pc sc
	pt' = nextPos pt s

        overlap1 pc sc pt s =
           case compare pc pt of
             LT -> litc (pc,sc1):overlap pt sc2 s
	       where (sc1,sc2) = split pc pt sc
             GT -> (t,(pt,s1)):overlap pc sc s2
	       where (s1,s2) = split pt pc s
	     EQ -> overlap pc sc s

        split pc pt (c:cs) | pc<pt = apFst (c:) (split (nextPos1 pc c) pt cs)
        split _ _ s = ("",s)

        overlap pc (c:cs) (' ':s) =
-}

    addSpace p0 [] = []
    addSpace p0 (t@(_,(p,s)):ts) =
       (if p0<p
        then ((Whitespace,(p0,space p0 p)):)
        else id) $ t:addSpace (nextPos p s) ts

    space (Pos _ y0 x0) (Pos _ y x) = vspace y0 x0 y x
    vspace y0 x0 y x =
      if y0<y
      then '\n':vspace (y0+1) 1 y x
      else replicate (x-x0) ' '
