
module Csv where

-- container
import Data.Tree (Tree(Node,rootLabel))

-- local imports
import qualified Language.Astview.Language as L
import Language.Astview.DataTree (data2tree)

-- Parsec (CSV Parser)
import Data.Generics hiding (Infix)
import Text.ParserCombinators.Parsec
import Text.Parsec.Combinator
import Text.ParserCombinators.Parsec.Expr

--import Text.Parsec.String
--import Text.Parsec.Char
--import Text.Parsec.Prim

csv =
  L.Language
    "CSV"
    []
    [".csv"]
    (const $ Left L.Err)
    (data2tree::[[String]] -> Tree String)
    Nothing
    Nothing

-- (parse csvFile "(unknown)")

-- Parsec (Simple CSV)
csvFile = endBy line eol
line = sepBy cell (char ',')
cell = many (noneOf ",\n")

eol :: Parser Char
eol = char '\n'

