module PreludeText where

type ShowS = String->String

class Show a where
  show :: a -> String
  showsPrec :: Int -> a -> ShowS
  showList :: [a] -> ShowS

  showsPrec _ x = showString (show x)

  show x        = showsPrec 0 x ""

  showList []       = showString "[]"
  showList (x:xs)   = showChar '[' . shows x . showl xs
		      where showl []     = showChar ']'
			    showl (x:xs) = showChar ',' . shows x .
					   showl xs

shows            :: (Show a) => a -> ShowS
shows            =  showsPrec 0

showString = (++)
showChar c s = c:s

showParenArg :: Int -> ShowS -> ShowS
showParenArg d = showParen (10<=d)

showParen        :: Bool -> ShowS -> ShowS
showParen b p    =  if b then showChar '(' . p . showChar ')' else p

showArgument x = showChar ' ' . showsPrec 10 x
