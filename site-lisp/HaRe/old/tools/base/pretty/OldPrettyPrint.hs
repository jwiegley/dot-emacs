--- This uses PrettyM, rather than Pretty, as its starting point.

module OldPrettyPrint(module PrettyM,module OldPrettyPrint) where

import PrettyM
import Ratio

-- class Printable is defined in PrettyM

-- A class to make it easier to print Haskell infix operators correctly:
class Printable a => PrintableOp a where
    ppiOp :: a -> Doc
{-      How to print operators "mod"   and "+":

	  ppi   should produce "mod"   and "+".
	  wrap  should produce "mod"   and "(+)".
	  ppiOp should produce "`mod`" and "+".      -}

-- A class to make it easier to print type applications like (,) a b and
-- [] Int in the normal way, (a,b) and [Int].
class Printable fun => PrintableApp fun arg where
  wrapApp,ppiApp :: fun -> [arg] -> Doc

-- Predefined instances:

instance Printable Char where
    ppi	    = char
    ppiList = text -- this defines how strings are printed, since String=[Char]
    wrap    = ppi

instance Printable Bool    where wrap = ppi
instance Printable Int     where wrap = ppi
instance Printable Integer where wrap = ppi
instance Printable Float   where wrap = ppi
instance Printable Double  where wrap = ppi
instance Integral a => Printable (Ratio a) where wrap = ppi

instance Printable a => Printable [a] where
    ppi  = ppiList
    ppis = map ppi
    wrap = ppi

instance Printable a => Printable (Maybe a) where
    ppi = maybe empty ppi
    wrap = maybe empty wrap

instance (Printable a, Printable b) => Printable (a, b) where
    ppi (a,b) = ppiFTuple [ppi a,ppi b]
    wrap = ppi

instance (Printable a, Printable b, Printable c) => Printable (a, b, c) where
    ppi (a,b,c) = ppiFTuple [ppi a,ppi b,ppi c]
    wrap = ppi

instance (Printable a, Printable b, Printable c, Printable d)
      => Printable (a, b, c, d) where
    ppi (a,b,c,d) = ppiFTuple [ppi a,ppi b,ppi c,ppi d]
    wrap = ppi

instance (Printable a, Printable b, Printable c, Printable d, Printable e)
      => Printable (a, b, c, d, e) where
    ppi (a,b,c,d,e) = ppiFTuple [ppi a,ppi b,ppi c,ppi d,ppi e]
    wrap = ppi

ppiTuple,ppiFTuple,wrapTuple,wrapSeq,wrapFTuple,wrapFSeq
    :: Printable a => [a] -> Doc

ppiTuple   = parens . ppiSeq
ppiFTuple  = parens . ppiFSeq
wrapTuple  = parens . wrapSeq
wrapSeq    = wrapSet comma
wrapFTuple = parens . wrapFSeq
wrapFSeq   = wrapFSet comma

wrapSet,wrapFSet :: Printable a => Doc -> [a] -> Doc

wrapSet  = wrapSep0 sep
wrapFSet = wrapSep0 fsep


wrapSep0 :: Printable a => ([Doc] -> Doc) -> Doc -> [a] -> Doc
wrapSep0 sepOp separator []  = empty
wrapSep0 sepOp separator [d] = wrap d
wrapSep0 sepOp separator ds  = sepOp $ punctuate separator $ map wrap ds


maybepp :: (a -> Doc) -> Maybe a -> Doc
maybepp pf (Just a) = pf a
maybepp _  Nothing  = empty

ppiBinOp lhs op rhs = sep [lhs<+>op,letNest rhs]

optpp b x = if b then ppi x else empty
