module PrettyDoc where
import TokenTags

data Layout = Horiz Sep | Vert | HorizOrVert Sep | Fill Sep deriving (Show)
data Sep = Cat | Sep deriving (Show)

nonEmpty Empty = False
nonEmpty d = True

data Doc
  = Empty
  | Char Char
  | Text String
  | Attr TokenTag Doc
  | Nest Int Doc
  | Group Layout [Doc]
  deriving (Show)

{-
class Doc doc where
  -- Required methods:
  empty :: doc
  text :: String->doc
  nest :: Int->doc->doc
  group :: Layout->[doc]->doc

  -- Methods with default implementations:
  char :: Char->doc
  char c = text [c]
-}
