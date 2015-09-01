{-

This File exports the list of known parsers for astview.
You can extend the list with your own parsers as proposed with the 
CustomParsers.hs module and the concatenation of the list.

Beware, this file will be overwritten when updating the package.

-}

module Language.Hareview.Languages.Languages where

-- container
import Data.Tree (Tree(..))

-- -- local imports
import Language.Hareview.Language 

-- import Haskell  -- requires haskell-src-exts
import Language.Hareview.Languages.HaskellGhcParser

-- | Main export for dynamic interpretation by astview
languages :: [Language]
languages = [haskellghc]

-- | A simple test function to launch parsers from ghci.
--   When this works, astview should work too.
-- testParser' :: Parser -> String -> IO ()
-- testParser' p s = putStrLn $ drawTree $ (tree p) s

-- t = testParser' (head $ reverse parsers) "main = putStrLn \"Hello World\""
