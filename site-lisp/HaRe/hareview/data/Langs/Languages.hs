{-

This File exports the list of known parsers for astview.
You can extend the list with your own parsers as proposed with the 
CustomParsers.hs module and the concatenation of the list.

Beware, this file will be overwritten when updating the package.

-}

module Languages where

-- container
import Data.Tree (Tree(..))

-- -- local imports
import Language.Astview.Language 

import Haskell  -- requires haskell-src-exts
import Csv -- requires parsec
import Expr -- requires parsec

-- | Main export for dynamic interpretation by astview
languages :: [Language]
languages = [haskellexts,expr,csv]

{-
-- --------------------------------------------------------

-- | Define a custom parser
linesAndWords :: Parser
linesAndWords = Parser "Lines and Words" [] [".law"] buildTreeLaw

buildTreeLaw = buildTreeGen (Just . map words . lines) data2tree
-}
