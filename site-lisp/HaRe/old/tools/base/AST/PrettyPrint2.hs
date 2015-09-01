{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances  #-}
module PrettyPrint2 where
import qualified PrettyDoc as P(Doc)
import PrettyDoc hiding (Doc)
import PrettyEnv
import TokenTags
import MUtils

type Doc = DocM P.Doc

class Show a => Printable a where
  ppi     :: a   -> Doc    -- Prettyprint Intelligently
  ppiList :: [a] -> Doc    -- Specialized for Char/String
  ppis    :: a   -> [Doc]  -- To allow for cases in which we can generate
                           -- a list of Docs from a given type
  wrap    :: a   -> Doc	   -- for bracketing

  ppi2    :: a   -> Doc    -- added by cmb21 differencing printing
                           -- guards in normal RHS and within alts.

  ppi     = plain

  ppiList = brackets . ppiFSeq
  ppis a  = [ ppi a ]
  wrap    = parens . ppi

-- Essential instances:
instance Show Doc where show (DocM d) = show (d defaultMode) -- useless?
instance Printable Doc  where ppi = id

instance Printable Char where
    ppi	c   = char c
    ppiList = text -- this defines how strings are printed, since String=[Char]
    wrap    = ppi

instance Printable a => Printable [a] where
    ppi  = ppiList
    ppis = map ppi
    wrap = ppi

-- A class to make it easier to print Haskell infix operators correctly:
class Printable a => PrintableOp a where
    isOp :: a -> Bool
    ppiOp :: a -> Doc
{-      How to print operators "mod"   and "+":

	  ppi   should produce "mod"   and "+".
	  wrap  should produce "mod"   and "(+)".
	  ppiOp should produce "`mod`" and "+".      -}

-- A class to make it easier to print type applications like (,) a b and
-- [] Int in the normal way, (a,b) and [Int].
class Printable fun => PrintableApp fun arg where
  wrapApp,ppiApp :: fun -> [arg] -> Doc


cdoc = DocM . const

-- Hughes/SimonPJ style pretty printing operators:

char   = cdoc . Char
text   = cdoc . Text
empty  = cdoc Empty
group l ds = DocM $ \e->Group l [de|DocM d<-map ppi ds,let de=d e,nonEmpty de]
nest n = fmap (nest' n) . ppi
  where
    nest' n (Nest n' d) = nest' (n+n') d
    nest' n d = Nest n d

-- Eta expansions because of the annying monomorphism restriction!
attr a = fmap (Attr a) . ppi
kw   d = attr Reserved d
var  d = attr Var d
con  d = attr Con d
varop d = attr VarOp d
conop d = attr ConOp d
tcon d = attr TCon d
lit  d = attr Lit d
cmnt d = attr Comment d
modn d = attr ModName d

a<>b = hcat [ppi a,ppi b]
a<+>b = hsep [ppi a,ppi b]
a$$b = vcat [ppi a,ppi b]

hcat ds = group (Horiz Cat) ds
hsep ds = group (Horiz Sep) ds
vcat ds = group Vert ds
cat  ds = group (HorizOrVert Cat) ds
sep  ds = group (HorizOrVert Sep) ds
fcat ds = group (Fill Cat) ds
fsep ds = group (Fill Sep) ds

plain x = text (show x)

punctuate p []     = []
punctuate p (d:ds) = go d ds
    where go d []     = [ppi d]
          go d (e:es) = (d <> p) : go e es

-- Additional pretty printing functions:
{-
ppiSeq :: Printable a => [a] -> Doc
ppiSet :: Printable a => Doc -> [a] -> Doc
ppiSep0 :: Printable a => ([Doc] -> Doc) -> Doc -> [a] -> Doc
ppiFSeq :: Printable a => [a] -> Doc
ppiFSet :: Printable a => Doc -> [a] -> Doc
ppiTuple :: Printable a => [a] -> Doc
ppiFTuple :: Printable a => [a] -> Doc
wrapTuple :: Printable a => [a] -> Doc
wrapSeq :: Printable a => [a] -> Doc
wrapSet :: Printable a => Doc -> [a] -> Doc
wrapFTuple :: Printable a => [a] -> Doc
wrapFSeq :: Printable a => [a] -> Doc
wrapFSet :: Printable a => Doc -> [a] -> Doc
wrapSep0 :: Printable a => ([Doc] -> Doc) -> Doc -> [a] -> Doc
-}

ppiSeq ds = ppiSet ',' ds

ppiSet s ds = ppiSep0 sep s ds

ppiSep0 sepOp separator []  = empty
ppiSep0 sepOp separator [d] = ppi d
ppiSep0 sepOp separator ds  = sepOp $ punctuate separator $ map ppi ds

ppiFSeq ds = ppiFSet ',' ds
ppiFSet s ds = ppiSep0 fsep s ds

ppiTuple ds = parens (ppiSeq ds)
ppiFTuple ds = parens (ppiFSeq ds)
wrapTuple ds = parens (wrapSeq ds)
wrapSeq ds = wrapSet ',' ds
wrapSet s ds = wrapSep0 sep s ds
wrapFTuple ds = parens (wrapFSeq ds)
wrapFSeq ds = wrapFSet ',' ds
wrapFSet s ds = wrapSep0 fsep s ds

wrapSep0 sepOp separator []  = empty
wrapSep0 sepOp separator [d] = wrap d
wrapSep0 sepOp separator ds  = sepOp $ punctuate separator $ map wrap ds


--maybepp :: (a -> Doc) -> Maybe a -> Doc
maybepp pf (Just a) = pf a
maybepp _  Nothing  = empty

optpp b x = if b then ppi x else empty

ppiBinOp lhs op rhs = sep [lhs<+>op,letNest rhs]

parenBinOp x op y = parens (ppiBinOp x op y) -- should consult infixParens!!

-- These are rather pointless, but kept around for backwards compatibility:
lparen = kw '('
rparen = kw ')'
lbrack = kw '['
rbrack = kw ']'
lbrace = kw '{'
rbrace = kw '}'
quote = kw '\''
dquote = kw '"'
bquote = kw '`'
equals = kw '='
comma = kw ','
float = plain :: Float->Doc
double = plain :: Double->Doc
space = ppi ' '

parens d = lparen<>d<>rparen
brackets d = lbrack<>d<>rbrack
braces d = lbrace<>d<>rbrace
doubleQuotes d = dquote<>d<>dquote
backQuotes d = bquote<>d<>bquote
{-
	quotes, charQuotes, backQuotes, doubleQuotes,
        quote, backQuote, doubleQuote, semi, comma, colon, space, equals,

        hang, punctuate,
-}

-- Environment manipulating functions:

withPPEnv :: PPHsMode -> Doc -> Doc
withPPEnv mode d = return $ (unDocM d) mode

updPPEnv f d = do e <- getPPEnv; withPPEnv (f e) d

doNotation :: Doc -> Doc
doNotation = updPPEnv (\e->e { insideDo = True })


doElseNest d = do e <- getPPEnv
		  if insideDo e then nest (doElseIndent e) (ppi d) else ppi d

ppIfDebug debug = ifM (debugInfo # getPPEnv) (ppi debug) empty
ppIfTypeInfo tinfo = ifM (typeInfo # getPPEnv) (ppi tinfo) empty

ppIfUnicode unicode ascii =
    ifM (useUnicode # getPPEnv)
        (ppi unicode)
        (ppi ascii)

withUnicode d = updPPEnv (\e->e{useUnicode=True}) d
withDebug   d = updPPEnv (\e->e{debugInfo=True}) d

classNest, doNest, caseNest, letNest, funNest, dataNest
  :: Printable a => a -> Doc
classNest = nest' classIndent
doNest    = nest' doIndent
caseNest  = nest' caseIndent
letNest   = nest' letIndent
funNest   = nest' funIndent
dataNest  = nest' dataIndent

nest' p d = do { e <- getPPEnv ; nest (p e) (ppi d) }

blankline :: Doc -> Doc
blankline d = do e <- getPPEnv
		 if spacing e && layoutType e /= PPNoLayout
		     then d
			  $$ space
		     else d

layout ds = do e <- getPPEnv
	       case layoutType e of
		 --PPSemiColon   ->
		 --PPUtrecht     ->
		 PPNoLayout    -> braces . hsep . punctuate ';' $ ds
		 _             -> vcat ds

-- Obsolete:
appParensOn = id
appParensOff = id

