{-

This File exports the list of known parsers for astview.
You can extend the list with your own parsers as proposed with the 
CustomParsers.hs module and the concatenation of the list.

Beware, this file will be overwritten when updating the package.

-}

module Language.Hareview.Languages.Parsers where

-- container
import Data.Tree (Tree(Node,rootLabel),drawTree)

-- -- local imports
import Language.Hareview.Parser (Parser (..))
import Language.Hareview.DataTree (flat,data2tree)
import Language.Hareview.Languages.HaskellGhcParser  

-- | Main export for dynamic interpretation by astview
parsers :: [Parser]
parsers = [haskellghc]

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
testParser' :: Parser -> String -> IO ()
testParser' p s = putStrLn $ drawTree $ (tree p) s

t = testParser' (head $ reverse parsers) "main = putStrLn \"Hello World\""
