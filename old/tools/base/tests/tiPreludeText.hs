module PreludeText where


type ShowS = String->String
class Show a where
   show :: a -> String
   showsPrec :: Int -> a -> ShowS

showString = (++)
showChar   =  (:)

-- Basic printing combinators (nonstd):
showParenArg :: Int -> ShowS -> ShowS
showParenArg d = showParen (10<=d)

showArgument x = showChar ' ' . showsPrec 10 x

showParen :: Bool -> ShowS -> ShowS
showParen b p    =  if b then showChar '(' . p . showChar ')' else p


lex :: ReadS String
lex = undefined

type ReadS a = String -> [(a,String)]
class Read a where
  read :: String -> a
  readsPrec :: Int -> ReadS a

-- Basic parsing combinators (nonstd):

readToken x t s = [(x,r)|(t',r)<-lex s,t'==t]

readParenArg :: Int -> ReadS a -> ReadS a
readParenArg d = readParen (10<=d)
readArgument s = readsPrec 10 s

readParen        :: Bool -> ReadS a -> ReadS a
readParen b g    =  if b then mandatory else optional
                    where optional r  = g r ++ mandatory r
                          mandatory r = [(x,u) | ("(",s) <- lex r,
                                                 (x,t)   <- optional s,
                                                 (")",u) <- lex t    ]



rf `readAp` rx = \ s0 -> [(f x,s2) | (f,s1)<-rf s0,(x,s2)<-rx s1]

readChoice rd1 rd2 s = rd1 s ++ rd2 s
