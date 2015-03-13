{-+
PrettyM redefines the combinators in Pretty, so that they pass an
environment around.  This can be used to adust the behaviour of the layout,
spacing etc., without parameterising the whole pretty printer.  To the user
it all appears the same.

May be useful to rewrite this as a state transformer, rather than a
state reader monad.  Could then set different display conditions for
subsections of the Parser.

See Pretty.lhs for description of the combinators.
-}
module PrettyM (module PrettyM, module PrettyEnv, P.Mode, P.TextDetails) where

import qualified Pretty as P
import Data.Ratio
import Control.Monad(liftM2,liftM)
import MUtils
import PrettyEnv

-- So that pp code still looks the same 
-- this means we lose some generality though
type Doc = DocM P.Doc

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

isEmpty :: Doc -> Bool
isEmpty d = P.isEmpty $ unDocM d defaultMode

nest :: Int -> Doc -> Doc
nest i m = fmap (P.nest i) m

classNest, doNest, caseNest, letNest, funNest, dataNest
  :: Printable a => a -> Doc
classNest = nest' classIndent
doNest    = nest' doIndent
caseNest  = nest' caseIndent
letNest   = nest' letIndent
funNest   = nest' funIndent
dataNest  = nest' dataIndent

nest' p d = do { e <- getPPEnv ; nest (p e) (ppi d) }

-- Literals

text, ptext :: String -> Doc
text  = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

litChar :: Char -> Doc
litChar = return . P.litChar

litString :: String -> Doc
litString = return . P.litString

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Integral a => Ratio a -> Doc
rational = return . P.rational

-- Simple Combining Forms

quotes, charQuotes, backQuotes, doubleQuotes, parens, brackets, curlies, braces
  :: Printable a => a -> Doc
quotes       = lift1 P.quotes
charQuotes   = lift1 P.charQuotes
backQuotes   = lift1 P.backQuotes
doubleQuotes = lift1 P.doubleQuotes
parens       = lift1 P.parens
brackets     = lift1 P.brackets
curlies      = lift1 P.curlies
braces       = curlies

lift1 f d = fmap f (ppi d)

-- Constants

quote, backQuote, doubleQuote :: Doc
quote       = return P.quote
backQuote   = return P.backQuote
doubleQuote = return P.doubleQuote

semi, comma, colon, space, equals :: Doc
semi   = return P.semi
comma  = return P.comma
colon  = return P.colon
space  = return P.space
equals = return P.equals

lparen, rparen, lbrack, rbrack, lcurly, rcurly :: Doc
lparen = return P.lparen
rparen = return P.rparen
lbrack = return P.lbrack
rbrack = return P.rbrack
lcurly = return P.lcurly
rcurly = return P.rcurly

-- Combinators

(<>), (<+>), ($$), ($+$) :: (Printable a,Printable b) => a -> b -> Doc
(<>) = lift2 (P.<>)
(<+>) = lift2 (P.<+>)
($$) = lift2 (P.$$)
($+$) = lift2 (P.$+$)

lift2 op m1 m2 = liftM2 op (ppi m1) (ppi m2)

hcat, hsep, vcat, sep, cat, fsep, fcat :: Printable a => [a] -> Doc
hcat  = liftList P.hcat
hsep  = liftList P.hsep
vcat  = liftList P.vcat
sep   = liftList P.sep
cat   = liftList P.cat
fsep  = liftList P.fsep
fcat  = liftList P.fcat

liftList f ds = fmap f (mapM ppi ds)

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do { d <- dM ; r <- rM ; return $ P.hang d i r }

-- Yuk, had to cut-n-paste this one from Pretty.hs
--punctuate :: Doc -> [Doc] -> [Doc]
punctuate p []     = []
punctuate p (d:ds) = go d ds
    where go d []     = [ppi d]
          go d (e:es) = (d <> p) : go e es



-- this is the equivalent of runM now.
renderWithMode :: PPHsMode -> Doc -> String
renderWithMode ppMode d = P.render . unDocM d $ ppMode

render :: Doc -> String
render = renderWithMode defaultMode

fullRenderWithMode :: PPHsMode -> P.Mode -> Int -> Float -> 
		      (P.TextDetails -> a -> a) -> a -> Doc -> a
fullRenderWithMode ppMode m i f fn e mD = 
		   P.fullRender m i f fn e $ (unDocM mD) ppMode


fullRender :: P.Mode -> Int -> Float -> (P.TextDetails -> a -> a) 
	      -> a -> Doc -> a
fullRender = fullRenderWithMode defaultMode

withPPEnv :: PPHsMode -> Doc -> Doc
withPPEnv mode d = return $ (unDocM d) mode

updPPEnv f d = do e <- getPPEnv; withPPEnv (f e) d

doNotation :: Doc -> Doc
doNotation = updPPEnv (\e->e { insideDo = True })


doElseNest d = do e <- getPPEnv
		  if insideDo e then nest (doElseIndent e) (ppi d) else ppi d

-- An attempt at intelligent recovery of parentheses in applications (used
-- currently only for types).  The first time appParens is called, it does not
-- parenthesize the given document, but changes the environment to ensure that
-- subsequent applications are. 
{-
appParens d = do e <- getPPEnv
		 if insideApp e
		    then parens d
		    else withPPEnv (e { insideApp = True }) d
-}

-- This sets insideApp to True without adding parens as well.
--appParensOn = id --updPPEnv (\e->e { insideApp = True })

-- This sets insideApp to False without adding parens as well.  Used when other
-- forms serve to parenthesize, e.g., to prevent [(M a)].
--appParensOff = id -- updPPEnv (\e->e { insideApp = False })


-- This is only used for lists where people most commonly put their _own_
-- curlies and semis.  It is not intended to recreate correct explicit layout
-- for Haskell programs, but merely to allow for pretty printing with curlies
-- and semis.  It might possibly be extendible into something to create
-- explicit layout.
{-
layout :: [Doc] -> Doc
layout []   = empty
layout docs = do e <- getPPEnv
		 case layoutType e of
		     PPSemiColon   ->
		         let (ds, d) = (init docs, last docs)
		         in
			     lcurly <+>
			     (vcat $
		              (map (\ d -> d <+> semi) ds) ++ [ d <+> rcurly ])
		     PPUtrecht     ->
		         let (d:ds) = docs
		         in
		             vcat $
			     (lcurly <+> d) :
			     map (semi <+>) ds ++
			     [ rcurly ]
		     _             ->
		         vcat docs
			 -- all others done as for classic (for the moment)
-}

blankline :: Doc -> Doc
blankline d = do e <- getPPEnv
		 if spacing e && layoutType e /= PPNoLayout
		     then d
			  $$ space
		     else d


ppIfDebug debug = ifM (debugInfo # getPPEnv) (ppi debug) empty

ppIfUnicode unicode ascii =
    ifM (useUnicode # getPPEnv)
        (ppi unicode)
        (ppi ascii)

withUnicode d = updPPEnv (\e->e{useUnicode=True}) d
withDebug   d = updPPEnv (\e->e{debugInfo=True}) d
--------------------------------------------------------------------------------

{-
  The Printable class is due to Urban Boquist.  We define instances for those
  types we want to pretty print.  It should also make the job of extensiblilty
  much easier.
-}

class (Show a{-, Eq a-}) => Printable a where
--  pp      :: a   -> String               -- Prettyprint
    ppi     :: a   -> Doc                  -- Prettyprint Intelligently
    ppiList :: [a] -> Doc                  -- Specialized for Char/String
    ppis    :: a   -> [Doc]                -- To allow for cases in which we
					   -- can generate a list of Docs from
					   -- a given type
    wrap    :: a   -> Doc		   -- for bracketing


--  pp      = render . ppi
    ppi     = text . show

    ppiList = brackets . ppiFSeq
    ppis a  = [ ppi a ]
    wrap    = parens . ppi

pp d = render (ppi d) -- pp used to be a method, but no instance defined it...

instance Show Doc where show = render

instance Printable Doc  where
    ppi = id

ppiSeq :: Printable a => [a] -> Doc
ppiSeq = ppiSet comma

ppiSet :: Printable a => Doc -> [a] -> Doc
ppiSet = ppiSep0 sep

ppiSep0 :: Printable a => ([Doc] -> Doc) -> Doc -> [a] -> Doc
ppiSep0 sepOp separator []  = empty
ppiSep0 sepOp separator [d] = ppi d
ppiSep0 sepOp separator ds  = sepOp $ punctuate separator $ map ppi ds

ppiFSeq :: Printable a => [a] -> Doc
ppiFSeq = ppiFSet comma

ppiFSet :: Printable a => Doc -> [a] -> Doc
ppiFSet = ppiSep0 fsep
