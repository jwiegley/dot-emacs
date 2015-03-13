-- Simple and efficient printing combinators
module PPrint where

infixr 2 &,!
infixr 1 !/

data Output = Sep | Str String | Nl | Indent Int

newtype Document = P ([Output] -> [Output])

class Printable a where
  pr :: a -> Document
  prList :: [a] -> Document

  prList = wpr

instance Printable Document where
  pr = id

nil = P id

nl = P (Nl:)
sep = P (Sep:)

indented x = indented' 2 x
indented' n x = P (Indent n:) ! x ! P (Indent (-n):)

vpr xs = foldr (!/) nil xs
wpr xs = prsep sep xs
hpr xs = foldr (!) nil xs

vmap f = foldr ((!/) . f) nil
wmap f xs = wpr (map f xs)
hmap f = foldr ((!) . f) nil

x !/ y = x ! nl ! y

x ! y = comp (pr x) (pr y)
  where comp (P x) (P y) = P (x . y)

x & y = x ! sep ! y

prsep s [] = nil
prsep s (x:xs) = x ! prpre s xs

prpre s [] = nil
prpre s (x:xs) = s ! x ! prpre s xs

instance Printable Char where
  pr c = P (Str [c]:)
  prList s = P (Str s:)

instance Printable a => Printable [a] where
  pr = prList

instance Printable Int where
  pr x = pr (show (x `asTypeOf` 1))

{-
instance Printable a => Printable (Maybe a) where
  pr Nothing = nil
  pr (Just x) = pr x
-}

pprint x = fmt0 0 (apply (pr x) [])
  where
    apply (P pr) = pr

    -- The printer is designed to avoid producing redundant spaces:
    --  + No indentation space on blank lines.
    --  + No trailing spaces at the end of lines.
    --  + No double spaces between items.
    
    -- fmt0: at the beginning of a line, before indentation has been made
    fmt0 n [] = []
    fmt0 n (Nl:os) = "\n"++fmt0 n os
    fmt0 n (Indent i:os) = fmt0 (n+i) os
    fmt0 n (Sep:os) = fmt0 n os
    fmt0 n (Str s:os) = space n++s++fmt n os

    space n = replicate (n `div` 8) '\t' ++ replicate (n `mod` 8) ' '

    -- fmt: in the middle of a line, after indentation and some text
    fmt n [] = []
    fmt n (o:os) =
      case o of
	Str s -> s++fmt n os
	Nl -> "\n"++fmt0 n os
	Indent i -> fmt (n+i) os
	Sep -> fmt1 n os

    -- fmt1: in the middle of a line, a space is to be inserted before next item
    fmt1 n [] = []
    fmt1 n (o:os) =
      case o of
        Str s -> ' ':s++fmt n os
	Nl -> "\n"++fmt0 n os
	Indent i -> fmt1 (n+i) os
	Sep -> fmt1 n os
