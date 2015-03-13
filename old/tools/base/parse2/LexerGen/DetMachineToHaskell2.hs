module DetMachineToHaskell2(dfaToHaskell,CaseOf(..),OutputFun(..)) where
import PPrint
import HaskellChars
import HsTokens
import List(partition,sort,sortBy,nub)
import DFA(DFA(..))
import qualified OrdMap as OM
import OpTypes(cmpBy)
import MUtils(collectBySnd)
import Trace(trace)

dfaToHaskell charclasses modname imports funname ((init,final),DFA dfa) =
    "module" & modname & "("!funname!")" & "where" & nl &
    vmap ("import"&) imports & nl &
    "type" & "Output" & "=" & "[(Token,String)]" & nl &
    "type" & "Input" & "=" & "String" & nl &
    "type" & "Acc"  & "=" & "Input" & "-- reversed" & nl &
    "type" & "Lexer"  & "=" & "Input -> Output" & nl &
    "type" & "LexerState"  & "=" & "(Acc->Lexer) -> Acc -> Lexer" & nl &
    nl &
    funname & "::" & "Lexer" & nl &
    funname & "is" & "=" & start init "is" & nl &
    nl &
    charclassfundef &
    statesToHaskell final charclassfun dfa
  where
    (charclassfundef,charclassfun) =
      case charclasses::(Maybe [(HaskellChar,Int)]) of
        Nothing -> (nil,id)
	Just ccs -> (charClassFunToHaskell ccs & nl,("cclass" &))

charClassFunToHaskell ccs =
    "cclass" & "::" & "Char" & "->" & "Int" & nl &
    "cclass" & "c" & "=" & nl &
    indented (haskellCharCase "c" show "0" ccs) & nl

state st = "state"!st
scall st err acc is = state st & err & acc & is -- state function call
lhs st is = scall st "err" "as" is -- lhs of state function

startstate st = "start"!st
start st is = startstate st & is -- (re)start from state 
startlhs st is = start st is -- lhs of state start function

statesToHaskell final ccfun dfa =
    vmap (stateToHaskell final (ccfun,alphabet)) states
  where
    states = OM.toList dfa
    alphabet =
      case errorValue of
	Just e ->  Just (e:nub [c|(_,(iedges,_))<-states,(c,_)<-iedges])
	Nothing -> Nothing

stateToHaskell final ccinfo ste@(st,(_,oedges)) =
    startdef &
    state st & "::" & "LexerState" & nl &
    stateToHaskell'' final ccinfo ste
  where
    -- If there are output edges, this state can't be a start state.
    startdef =
      if null oedges
      then startstate st & "::" & "Lexer" & nl &
           startlhs st "is" & "=" & scall st err (show "") "is" & nl
      else nil

    err = "("!"\\"&"as"&"is"&"->"&oedgesToHaskell "is" oedges !")"

stateToHaskell'' final ccinfo (st,([],oedges@(_:_))) =
  lhs st "is" & "=" & indented (oedgesToHaskell "is" oedges) & nl
stateToHaskell'' final ccinfo (st,es@(_,oedges)) =
  lhs st "[]" & "=" & indented (eofEdge st final oedges) & nl &
  lhs st "iis@(i:is)" & "=" &
  stateToHaskell' ccinfo es & nl

eofEdge st final []     | st `elem` final = "gotEOF" & "as"
eofEdge _  _     oedges                   =
    opterrfun oedges "[]" ("err"&"as"&"[]")
    --oedgesToHaskell "[]" oedges

stateToHaskell' ccinfo ([],    oedges) = oedgesToHaskell "iis" oedges
stateToHaskell' (ccfun,Just allClasses) (iedges@(_:_),oedges) =
  nl &
  indented (opterrfun oedges "iis"(
    caseExp (ccfun (pr"i"))
            opt_iedgeToHaskell'
	    (opt_iedgeToHaskell' iedge')
	    iedges''))
  where
    (_,iedge'):iedges' = sortBy order $
			 collectBySnd [(c,lookup c iedges)|c<-allClasses]
    order = cmpBy (negate.length.fst)
    iedges'' = [(c,st)|(cs,st)<-iedges',c<-cs]

    opt_iedgeToHaskell' = maybe ("err"&"as"&"iis") iedgeToHaskell'

stateToHaskell' (ccfun,Nothing) (iedges,oedges) =
  nl &
  indented (opterrfun oedges "iis"(
    caseExp (ccfun (pr"i"))
            iedgeToHaskell'
	    ("err"&"as"&"iis") -- (oedgesToHaskell "iis" oedges)
	    iedges))

opterrfun oedges iis body =
    if null oedges
    then body
    else body&nl&"where"&"err"&"_ _"&"="&oedgesToHaskell iis oedges
{-
    else "let"&"err"&"_ _"&"="&oedgesToHaskell iis oedges & nl &
	  "in"&body
-}
--iedgesToHaskell = vpr . map iedgeToHaskell
--iedgeToHaskell (c,st) = show c & "->" & iedgeToHaskell' st

iedgeToHaskell' st = scall st "err" "(i:as)" "is"

oedgesToHaskell is = oedgesToHaskell' "as" is
oedgesToHaskell' as is [] = "gotError" & as & is
oedgesToHaskell' as is [oedge] = oedgeToHaskell as is oedge
oedgesToHaskell' as is oedges0 =
  trace msg $
  oedgeToHaskell as is oedge
  -- & nl & "--" & msg
  where
    -- On ambiguities, make a choice by comparing token classes:
    oedges = sort oedges0
    oedge = last oedges -- give priority to later tokens in the token data type
    msg = "Machine is nondeterministic: "++show oedges
oedgeToHaskell as is (os,st) =
-- "("!show os!","&"reverse"&"as"!")"&":"&state st & show "" & is
  output os (pr as) (pr st) (pr is)


--

class Show token => OutputFun token where
  output :: token -> Document -> Document -> Document -> Document

  output = default_output

default_output token as next is =
  "output" & show token & as & "("!startstate next & is !")"

instance OutputFun Token where
  output token as next is =
    case token of
      NestedCommentStart -> "nestedComment" & as & is & state next
      _ -> default_output token as next is

class CaseOf a where
  caseExp :: (Printable exp,Printable rhs) =>
             exp -> (v->rhs) -> rhs -> [(a,v)] -> Document
  errorValue :: Maybe a
  errorValue = Nothing

--

instance CaseOf HaskellChar where caseExp = haskellCharCase

haskellCharCase e rhs defaultrhs cases =
    caseE e (haskelLCharCaseBranches cases)
  where
    haskelLCharCaseBranches cases =
      case partition (isAscii . fst) cases of
	(as,us) -> vpr' (map asciiCharClass as++[uniCharClasses us])

    isAscii (ASCII _) = True
    isAscii _ = False

    asciiCharClass (ASCII c,n) = show c & "->" & rhs n

    uniCharClasses [] = "_" & "->" & defaultrhs
    uniCharClasses us =
      "c" & indented (
        vpr' $ ("|" & "isAscii" & "c" & "->" & defaultrhs):
	      map uniCharClass us ++
	      [defaultcase])

    uniCharClass (u,n) = "|" & tstFunc u & "c" & "->" & rhs n

    defaultcase = "|" & "otherwise" & "->" & defaultrhs

    tstFunc u =
      case u of
        UniWhite -> "isSpace"
	UniSymbol -> "isSymbol"
	UniDigit -> "isDigit"
	UniLarge -> "isUpper"
	UniSmall -> "isLower"

instance CaseOf Int where caseExp = simpleCase; errorValue=Just 0
instance CaseOf Char where caseExp = simpleCase

simpleCase e rhs defaultrhs cases =
    caseE e (branches cases)
  where
    branches cases = vpr' (map branch cases++[defaultbranch])

    branch (a,v) = show a & "->" & rhs v
    defaultbranch = "_" & "->" & defaultrhs

vpr' = prsep nl

caseE e bs = "case" & e & "of" & nl & indented bs
