{-+
This module defines the function #hlex2html#, which translates the output from
an early pass of the lexical analyzer to HTML. It can also make use of cross
reference information to link identifiers to their definitions.

The generated HTML is intended to be part of the body of a web page,
thus it does not include the #head# or #body# tags.
-}
module HLex2html({-hlex2html,-}hlex2html',simpleHlex2html) where
import RefsTypes --hiding (isDef)
import MUtils(apSnd)
import Data.Char(isSpace{-,isAlpha-},isAlphaNum)
import HsTokens
import SrcLoc1
import LitTxt(toHTMLblock)
import PathUtils(normf)
import HLexTagModuleNames
import PrettyPrint(pp)

--------------------------------------------------------------------------------
type ModuleContext = (FilePath,[(FilePath,Module)]) -- (this,other) modules
type LexTokens = [(Token,(Pos,String))]
type URL = String
type HTML = String

simpleHlex2html :: LexTokens -> HTML
--hlex2html  :: ModuleContext -> (Refs,LexTokens) -> HTML
hlex2html' :: (Module->URL) -> ModuleContext -> (Refs,LexTokens) -> HTML
--------------------------------------------------------------------------------

simpleHlex2html = hlex2html' undefined dummy . (,) []
  where dummy = ("",[("",noModule)])

hlex2html' srcURL (thisf,fm) =
     normal . tokens2html srcURL (thisf,thism,fm) . uncurry merge .
     apSnd convModuleNames
  where Just thism = lookup thisf fm

{-+
The functions #normal#, #pre#, and #code# implement a state machine that
handles the insertion of properly nested #pre# and #div# tags.
-}

-- Normal text mode, in which literate comments can be output:
normal [] = []
normal ((LiterateComment,(_,s)):ts) = toHTMLblock s++normal ts
normal ((Whitespace,(p,s)):ts) | noCodeOnLine (line p) ts = s++normal ts -- indented code??
normal ((Commentstart,(Pos{column=1},s1)):(Comment,(_,s2)):ts) =
        preStart++cmntesc (s1++s2)++pre ts
normal ((Comment,ps1):(Whitespace,ps2):ts) | isBlockComment ps1 ps2 =
        preStart++cmntesc (snd ps1++snd ps2)++pre ts
normal ts = codeStart++code ts

-- Inside a <pre> block, where blank lines and block comments can be output:
pre [] = preEnd
pre ((LiterateComment,(_,s)):ts) = preEnd++toHTMLblock s++normal ts
pre ((Whitespace,(_,s)):ts) = s++pre ts
pre ((Commentstart,(Pos{column=1},s1)):(Comment,(_,s2)):ts) =
        cmntesc (s1++s2)++pre ts
pre ((Comment,ps1):(Whitespace,ps2):ts) | isBlockComment ps1 ps2 =
        cmntesc (snd ps1++snd ps2)++pre ts
pre ts = preEnd++codeStart++code ts

-- Inside a code, where code and ordinary comments can be output:
code [] = codeEnd
code ((LiterateComment,(_,s)):ts) = codeEnd++toHTMLblock s++normal ts
code ((Commentstart,(_,s1)):(Comment,(_,s2)):ts) = cmntesc (s1++s2)++code ts
code ((Comment,ps1):(Whitespace,ps2):ts) | isBlockComment ps1 ps2 =
        codeEnd++preStart++cmntesc (snd ps1++snd ps2)++pre ts
code ((Comment,(_,s))   :ts) = cmntesc s++code ts
code ((Whitespace,(_,s))   :ts) = s++code ts
code ((_,(_,s)):ts) = s++code ts

preStart = "<pre>"
preEnd = "</pre>"
codeStart = "<div class=code><pre>"
codeEnd = "</pre></div>"

isBlockComment (Pos{column=1},'{':'-':_) (_,s) | '\n' `elem` s = True
isBlockComment _ _ = False

noCodeOnLine l ts =
    all ((`elem` notCode).fst) (takeWhile ((==l).line.fst.snd) ts)
  where notCode = [LiterateComment,Whitespace{-,Commentstart,Comment-}]

cmntesc = cmnt . esc

--------------------------------------------------------------------------------

tokens2html srcURL rs = map (token2html srcURL rs)

token2html :: (Module->URL)->(FilePath,Module,[(FilePath,Module)])->
	      ((Token,(Pos,String)),Maybe Orig)->
	      (Token,(Pos,String))
token2html _      _    ((LiterateComment,ps@(_,"> ")),_) = (Whitespace,ps)
token2html _      _                ((NestedComment,s),_) = nestedcomment s
token2html srcURL (thisf,thism,fm) ((t,(p,s)),r) = (t,(p,f (esc s)))
  where
    moduleLink s = 
      case [m|(f,m)<-fm,sameModuleName s m] of
        [m] -> link (srcURL m)
	_ -> modname
    f = case t of
	  ModuleName -> if sameModuleName s thism || thism==noModule
		        then modname
		        else moduleLink s
	  ModuleAlias -> modname
	  Reservedid -> b
	  Reservedop -> b
	  Conid -> conp
	  Consym -> consymp
	  Qconid -> conp
	  Qconsym -> consymp
	  Varid -> varp
	  Specialid -> b
	  Varsym -> varsymp
	  Qvarid -> varp
	  Qvarsym -> varsymp
--	  Literal -> lit -- obsolete
          IntLit -> lit
          FloatLit -> lit
	  CharLit -> lit
	  StringLit -> lit
	  {-
	  Whitespace -> 
	  Special
	  -}
	  _ -> id
    varp = var (info "var" "" p)
    conp = con (info "con" "" p)
    varsymp = var (info "var" "op" p)
    consymp = con (info "con" "op" p)
    modname = con (Nothing,[("class","mod")])

    info cl op p =
      case r of
	Just (n,role,sp,rs) | n==s ->
	    (link,
	     (if isDef role
	     then (("id",rstarget sp rs):)
	     else id) $
	       [("class",ty++cl++op),("title",n++": "++title)])
          where
            ty = if isType sp then "t" else ""
            ttag t = if isType t then "t" else "v"

	    link = case links of
		     [Just link] -> Just link
		     _ -> Nothing
	    title = case titles of
		      [] -> "not in scope"
		      _  -> unwords titles
	    (links,titles) = unzip (map shr rs)


	    sht T = "type"
	    sht V = "value"
	    sht Cl = "class"
	    sht (Co n) = "constructor of "++n
	    sht (Me n) = "method of class "++n
	    sht (Fi n) = "field of type "++n

            shr (t,p) =
		apSnd (("a "++sht t)++) $
		if role==DP
		then (Nothing," bound here")
		else if isDef role
	             then (Nothing," defined here")
		     else shrp t p
	    shrp t (Left (m,n)) =
	      if m==thism
	      then (Just ("#"++tmangle t n)," defined in this module")
	      else (Just (srcURL m++"#"++tmangle t n)," defined in module "++pp m)
	    shrp _ (Right p'@(f,rc)) =
		if p'==(thisf,p)
		then (Nothing," defined here")
		else if f==thisf
		     then (Just ("#"++shPos' rc),
		           " defined in this module at "++shPos rc)
		     else (Just (srcURL m++"#"++shPos' rc),
		           " defined in module "++pp m++" at "++show p')
	      where Just m = lookup (normf f) fm

	    --shpos (f,(y,x)) = show (SrcLoc f 0 y x) -- hmm
	    --shrc (y,x) = show y++":"++show x
	    --shrc' (y,x) = show y++"."++show x

            rstarget t = rtarget t . head
	    rtarget t = either (gtarget t) ptarget . snd
	    gtarget t = tmangle t . snd
	    ptarget = shPos' . snd
	    tmangle t p = ttag t++mangle p
 
	_ -> (Nothing,attrs)
         where
           attrs = if thism==noModule
		   then [("class",cl++op)]
		   else [("title","Hmm. Info missing")]

--isDef r =  r `elem` [DT,DL,DP,DC]

b = ctx "b"
var (optl,as) = optlink optl . ctx' "var" as
con (optl,as) = optlink optl . ctx' "b"  as
lit = ctx' "span" [("class","lit")]

optlink = maybe id link
link url = ctx' "a" [("href",url)]

cmnt = ctx' "span" [("class","cmnt")]

-- Some nested comments, {-+ ... -}, are treated like literate comments...
nestedcomment ps@(p,s) =
  case s of
    '{':'-':'+':c:s' | isSpace c ->
         case reverse s' of
           '}':'-':s -> (LiterateComment,(p,reverse s))
           _ -> (NestedComment,ps) -- Can't happen
    _ -> (NestedComment,ps)

ctx t s = tag t++s++endtag t
ctx' t as s = tag (t++shas as)++s++endtag t
  where
    shas = concatMap sha
    sha (n,v) = ' ':n++"="++quote v

tag t = "<"++t++">"
endtag t = tag ('/':t)

esc = concatMap esc1
  where esc1 '<' = "&lt;"
	esc1 '&' = "&amp;"
	esc1 c = [c]

quote s =
  if all isAlphaNum s
  then s
  else '"':s++"\""

mangle = concatMap mangle1
  where
    mangle1 c = if isAlphaNum c
		then [c]
		else '.':show (fromEnum c) -- hmm
