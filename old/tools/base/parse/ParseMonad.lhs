-----------------------------------------------------------------------------
Haskell Parser Monad
-----------------------------------------------------------------------------

\begin{code}
module ParseMonad where

import SrcLoc
import SrcLocPretty
--import HsAssoc
--import IOExts(trace)
import PrettyPrint
\end{code}

\begin{code}
data ParseResult a
    = Ok ParseState a
    | Failed String
      deriving Show

data LexContext
    = NoLayout
    | Layout Int
      deriving (Eq, Ord, Show)

--type  ParseState env = (env, [LexContext])
type  ParseState = [LexContext]

--type PM a = PME OperatorEnv a
--type PM a = PME a

newtype PM a 
    =  PM (String		-- input string
          -> SrcLoc		-- location of last token read
	  -> Int		-- current column
	  -> ParseState   	-- layout info. and infix operator environment
	  -> ParseResult a)

unPM (PM p) = p

thenPM :: PM a -> (a -> PM  b) -> PM  b
m `thenPM` k = PM $ \i l c s -> 
	       case (unPM m) i l c s of 
	       Failed s -> Failed s
	       Ok s' a  -> case k a of PM k' -> k' i l c s'

-- m `thenPM_` k = m `thenPM ` \_ -> k

-- same as mapM
{-
mapP :: (a -> P b) -> [a] -> P [b]
mapP f []     = returnP []
mapP f (a:as) = 
     f a       `thenP` \b ->
     mapP f as `thenP` \bs ->
     returnP (b:bs)
-}

returnPM a = PM $ \i l c s -> Ok s a

parseFile (PM p) f s =
    case p s  (SrcLoc f 1 1) 0 [] of
      Ok state mod -> return mod -- No rewriting here
      Failed err -> fail err

runPM (PM p) i l c s =
    case p i l c s of
        Ok _ a -> a
	Failed err -> error err

failPM :: String -> PM a
failPM err = PM $ \i l c s -> Failed err

getSrcLoc :: PM SrcLoc
getSrcLoc = PM $ \i l c s -> Ok s l

getContext :: PM [LexContext]
getContext = PM $ \i l c s -> Ok s s

--getInfixEnv :: PM env
--getInfixEnv =  PM $ \i l c s -> Ok s (fst s)

--setInfixEnv e  =  PM $ \i l c s -> Ok (e, snd s) ()


pushContext :: LexContext -> PM ()
pushContext ctxt =
    -- trace ("pushing lexical scope: " ++ show ctxt ++"\n") $
    PM $ \i l c s -> Ok (ctxt:s) ()


popContext :: PM ()
popContext = PM $ \i loc c stk ->
    case stk of
    (_:s) -> --trace ("popping lexical scope, context now " ++ show s ++ "\n") $
	     Ok s ()
    []    -> Failed $ render $
             hcat [ ppi loc, 
	            text ": parse error (possibly incorrect indentation)" ]


instance Monad PM where
    (>>=)  = thenPM 
    return = returnPM 
--  fail   = failPM
    fail = parseError

parseError :: String -> PM a
parseError err =
    PM $ \r loc -> (unPM $ fail $ pp loc ++ ": " ++ err ++ "\n") r loc
\end{code}
