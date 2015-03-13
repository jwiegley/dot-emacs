{-

This File exports the list of known parsers for astview.
You can extend the list with your own parsers as proposed with the 
CustomParsers.hs module and the concatenation of the list.

Beware, this file will be overwritten when updating the package.

-}

module Parsers where

-- container
import Data.Tree (Tree(Node,rootLabel),drawTree)

-- -- local imports
import Language.Astview.Parser (Parser (..))
import Language.Astview.DataTree (flat,data2tree)
import HaskellGhcParser  -- requires haskell-src-exts
-- import CsvParser      -- requires parsec
-- import ExprParser     -- requires parsec

-- | Main export for dynamic interpretation by astview
parsers :: [Parser]
parsers = [linesAndWords 
          ,haskellghc]

-- --------------------------------------------------------

-- | Define a custom parser
linesAndWords :: Parser
linesAndWords = Parser "Lines and Words" [".law"] treeLinesAndWords

-- | Seperate tree construction from parsing.
treeLinesAndWords :: String -> Tree String
treeLinesAndWords s = flat $ data2tree $ parseLinesAndWords s

-- | This simply parses
parseLinesAndWords :: String -> [[String]]
parseLinesAndWords s = map words (lines s)


-- | A simple test function to launch parsers from ghci.
--   When this works, astview should work too.
testParser :: Parser -> String -> IO ()
testParser p s = putStrLn $ drawTree $ (tree p) s

t = testParser (head $ reverse parsers) "main = putStrLn \"Hello World\""
