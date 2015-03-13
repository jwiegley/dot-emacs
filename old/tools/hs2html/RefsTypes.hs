module RefsTypes(module RefsTypes,Pos(..),sameModuleName,noModule) where
import HsName(ModuleName,sameModuleName,noModule)
import HsLexerPos(Pos(..))
import SrcLoc1(SrcLoc)
{-+
The cross reference information was once written to files by #tstModules#
and then read by #hs2html#. That is why there were #Show# and #Read# instances,
and why the constructor names are short.
<p>
Since hs2html has been integrated into pfe now, these types are rather
obsolete...
-}

--data SP = T | V deriving (Read)
data T = V | Co Name {-Ref-} | Me Name {-Ref-} | Fi Name {-Ref-} | T | Cl deriving (Eq,Show,Read)
data R = DT | DL | DC | DI | DP | U | Ex | Im deriving ({-Show,Read,-}Eq)
type Module = ModuleName
type Name = String
--type Pos = (Int,Int) -- (line,column)
type SrcPos = (FilePath,Pos) -- better to keep SrcLoc?
type Global = (Module,Name)
type Local = SrcPos
type Ref = Either Global Local
type Orig = (Name,R,T,[(T,Ref)])
type Refs = [(Pos,Orig)]

isDef U = False
isDef DI = False
isDef Ex = False
isDef Im = False
isDef _ = True

isType Cl = True
isType T = True
isType _ = False

shPos p = show (line p)++":"++show (column p)
shPos' p = show (line p)++"."++show (column p)

-- Merge a sorted list of reference info with a list of lexical tokens
-- (Designed to be lazy in the reference list)
merge rs [] = []
merge rs tts@(t@(_,(tp,_)):ts) = (t,optref):merge rs' ts
  where
    (optref,rs') = findref rs

    findref [] = (Nothing,[])
    findref rrs@((rp,ref):rs) =
	  case compare rp tp of
	    LT -> findref rs
	    EQ -> (Just ref,rs)
	    GT -> (Nothing,rrs)

{-
-- Strict merge (only marginally faster, it seems):
merge' rs [] = []
merge' [] ts = map (flip (,) Nothing) ts
merge' rrs@(r@(rp,ref):rs) tts@(t@(_,(tp,_)):ts) =
  case compare rp tp of
    LT -> merge' rs tts
    EQ -> (t,Just ref):merge' rs ts
    GT -> (t,Nothing):merge' rrs ts
-}
