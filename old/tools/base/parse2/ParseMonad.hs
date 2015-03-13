{-+
This module defines the parser monad, and the function #parseFile#, which is
the only way to invoke a parser.
-}
module ParseMonad(thenPM,PM,HToken,returnPM,parseError,getSrcLoc,
	          State,get,set,setreturn,eof,eoftoken,
		  parseFile,parseTokens) where
import HsTokens(Token(GotEOF))
import HsLexerPass1(lexerPass1Only,lexerPass0,Pos(..),line,column)
import MUtils
import SrcLoc1
import SrcLocPretty
import PrettyPrint(pp)
import Control.Monad.Error
--import Control.Monad(liftM,MonadPlus(..))
import Control.Monad
import ExceptM()
 --import IOExts(trace) -- for debugging only

default(Int)

type HToken = (Token,(SrcLoc,String))
 --type Pos = (Int,Int)
type Error = String
type LayoutContext = Int
type State = ([HToken],[LayoutContext])

-- Parser monad type:
newtype PM a = PM {unPM::(State->Either ParseMonad.Error (a,State))} 

returnPM x = PM $ Right . (,) x
PM p1 `thenPM` xp2 = PM $ \ts -> p1 ts >>= uncurry (unPM . xp2) -- =<< p1 ts
failPM msg = PM $ \ _ -> Left msg

{-
emapPM f (PM p) = PM $ \ ts -> case p ts of
				 Right ans -> Right ans
				 Left err -> Left (f err)
-}

get = PM $ \ st -> Right (st,st)
set st = PM $ \ _ -> Right ((),st)
setreturn x st = PM $ \ _ -> Right (x,st)

instance Monad PM where
  return=returnPM
  (>>=) = thenPM
  fail = parseError

{-instance Monad (Either String) where
    (Left a)  >>= _ = Left a
    (Right b) >>= f = f b
    return          = Right
    fail a          = Left a -}

instance Functor PM where fmap = liftM

instance MonadPlus PM where
  mzero = fail "parser failed"
  PM p1 `mplus` PM p2 = PM $ \ s -> case p1 s of
			              y@(Right _) -> y
				      Left _ -> p2 s

getSrcLoc = fst.snd # peek

peek = tok1 # get
  where
    tok1 (ts,_) = case ts of
		    t:_ -> t
		    []  -> eoftoken

parseError msg = err =<< peek
  where err (t,(p,s)) =
            failPM $ pos++": "++msg
          where pos = if p==eof
	              then "at end of file"
	              else pp p++", before "++s

parseFile pm f = parseTokens pm f . lexerPass0

parseTokens (PM p) f ts =
  case p (map convPos $ lexerPass1Only ts,initial_layout_context_stack) of
    Left err    -> fail ({-f++": "++-}err)
    Right (x,_) -> return x
  where
    convPos (t,(Pos n l c,s)) = {-seq loc-} (t,(loc,s))
      where loc = SrcLoc f n l c

eoftoken = (GotEOF,(eof,""))
eof = SrcLoc "?" 0 (-1) (-1) -- hmm

initial_layout_context_stack = []
