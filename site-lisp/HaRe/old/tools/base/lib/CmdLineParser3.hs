{- # OPTIONS -fglasgow-exts # -}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverlappingInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module CmdLineParser3(
  P((:--),Token),cmd,(!),(<@),( #@ ),chk,nil,many,arg,kw,opt,flag,named,
  run,usage,parseAll
  ) where
import PrettyPrint hiding (kw)
import Control.Monad(msum,join,liftM,MonadPlus(..),ap)
import Data.Maybe(isJust)
import System.Environment(getArgs)

infixl 3 <@,`chk`,#@
infix 2 :--
infixr 1 :!,!

data P res
  = Return res
  | forall arg . Ap (P (arg->res)) (P arg)
  | Named String (P res)
  | P res :-- String
  | Token (String->Maybe res) String
  | P res :! P res
  | forall item . Many (res->[item]) ([item]->res) (P item)

instance Functor P where fmap f p = Return f `Ap` p

chk p p' = const `fmap` p `Ap` p'
cmd s p = Return p `chk` kw s

f #@ p = fmap f p
(!) = (:!)
(<@) = Ap
nil = Return
arg = Token Just
many p = Many id id p
kw s = Token check s
  where check a = if a==s then Just () else Nothing

opt p = fmap Just p ! nil Nothing
flag s = isJust `fmap` opt (kw s)
named = Named

usage prefix p = pp (usageDoc prefix p)
usageDoc prefix p =
    sep [ppi "Usage:", nest 4 (prefix<+>main)] $$
    if null aux
    then empty
    else sep [nest 2 "where", nest 4 (vcat aux)]
  where
    (main,aux) = usage' p

    usage' :: P a -> (Doc,[Doc])
    usage' p =
      case p of
        Return _ -> (empty,[])
	Ap p1 p2 -> (m1<+>m2,a1++a2)
          where (m1,a1) = usage' p1
		(m2,a2) = usage' p2
	Named s p -> (nt,sep [nt<+>"=",nest 2 m]:a)
          where nt = "<"<>s<>">"
                (m,a) = usage' p
        p :-- s -> (m<+>"--"<+>s,a) where (m,a) = usage' p
        Token to s -> (text s,[])
	p1 :! Return _ -> (brackets m,as)
          where (m,as) = usage' p1
	p1 :! p2 -> (vcat ms,concat as)
          where (ms,as) = unzip (map usage' [p1,p2])
        Many _ _ p -> (braces m,a) where (m,a) = usage' p

run p = parseAll p =<< getArgs

parseAll p args =
  case unPM (parse p) args of
    Right (r,[]) -> r
    Right (_,args) -> fail $ "Unrecognized arguments: "++unwords args
    Left (args,errs) ->
        fail $ ('\n':) $
            pp $ "Expected one of:"<+>ppiFSeq errs
               $$ (if null args then empty else "Found: "<+>sep args)
	       -- $$ usageDoc p
               $$ text ""

newtype PM res = PM {unPM ::[String] -> Either ([String],[String]) (res,[String])}

instance Functor PM where fmap = liftM
instance Monad PM where
  fail s = PM $ \ args->Left (args,[s])
  return x = PM $ \args->Right (x,args)
  PM p1>>=xp2 = PM $ \ args->case p1 args of
			       Left err -> Left err
			       Right (x,args') -> unPM (xp2 x) args'
instance MonadPlus PM where
  mzero = fail "no parse"
  mplus (PM p1) (PM p2) =
    PM $ \ args -> case (p1 args,p2 args) of
		     (Right res,_) -> Right res
		     (r1@(Left (a1,errs1)),r2@(Left (a2,errs2))) ->
			 case compare (length a1) (length a2) of
                           LT -> r1
			   EQ -> Left (a1,errs1++errs2)
			   GT -> r2
		     (_,r2) -> r2

get = PM $ \ args -> Right (args,args)
set args = PM $ \ _ -> Right ((),args)

parse :: P res -> PM res
parse p =
  case p of
    Return res -> return res
    Ap pf pa -> parse pf `ap` parse pa
    Named _ p -> parse p
    p :-- s -> parse p
    Token check s ->
      do args <- get
	 case args of
	   a:as -> maybe (fail s)
			 (\a->set as>>return a)
			 (check a)
	   [] -> fail s
    p1 :! p2 -> parse p1 `mplus` parse p2
    Many to from p ->
        parse (cons `fmap` p `Ap` Many to from p ! Return (from []))
      where cons x xs = from (x:to xs)

{-
run :: Cmd m a -> m a

cmd :: String -> m a -> Cmd m a

ap :: Cmd m (a->b) -> Arg m a -> Cmd m b
chk :: P m a -> P m () -> P m a

kw :: String -> P m ()
alt :: P m a -> P m a -> P m a
alts :: [P m a] -> P m a

some,many :: P m a -> P m [a]
opt :: P m a -> P m (Maybe a)

flag :: String -> String -> Bool -> P m Bool
flag name desc def = 
-}
