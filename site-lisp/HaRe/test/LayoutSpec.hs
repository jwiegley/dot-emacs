module LayoutSpec (main, spec) where

import           Test.Hspec

import qualified GHC        as GHC

-- import qualified GHC.SYB.Utils as SYB


import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TokenUtils
-- import Language.Haskell.Refact.Utils.Layout
import Language.Haskell.Refact.Utils.TypeSyn

import Language.Haskell.TokenUtils.GHC.Layout
import Language.Haskell.TokenUtils.Layout
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.Utils

import TestUtils

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  -- ---------------------------------------------

  describe "allocTokens" $ do
    it "allocates Tokens for a default main module" $ do
      (t,toks) <- parsedFileBare
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      -- (SYB.showData SYB.Parser 0 parsed) `shouldBe` ""

      (show toks) `shouldBe`
         "[((((3,1),(3,5)),ITvarid \"main\"),\"main\"),"++
          "((((3,6),(3,7)),ITequal),\"=\"),"++
          "((((3,8),(3,16)),ITvarid \"putStrLn\"),\"putStrLn\"),"++
          "((((3,17),(3,24)),ITstring \"hello\"),\"\\\"hello\\\"\")]"

      let layout = allocTokens parsed toks
      (show $ retrieveTokens layout) `shouldBe` (show toks)
      (invariant layout) `shouldBe` []
      (showGhc layout) `shouldBe`
         "Node\n"++
         "  Entry (((ForestLine False 0 0 3), 1),\n"++
         "         ((ForestLine False 0 0 3), 24)) NoChange []\n"++
         "  [Node\n"++
         "     Entry (((ForestLine False 0 0 3), 1),\n"++
         "            ((ForestLine False 0 0 3),\n"++
         "             5)) NoChange [((((3,1),(3,5)),ITvarid \"main\"),\"main\")]\n"++
         "     [],\n"++
         "   Node\n"++
         "     Entry (((ForestLine False 0 0 3), 6),\n"++
         "            ((ForestLine False 0 0 3), 24)) NoChange []\n"++
         "     [Node\n"++
         "        Entry (((ForestLine False 0 0 3), 6),\n"++
         "               ((ForestLine False 0 0 3),\n"++
         "                7)) NoChange [((((3,6),(3,7)),ITequal),\"=\")]\n"++
         "        [],\n"++
         "      Node\n"++
         "        Entry (((ForestLine False 0 0 3), 8),\n"++
         "               ((ForestLine False 0 0 3), 24)) NoChange []\n"++
         "        [Node\n"++
         "           Entry (((ForestLine False 0 0 3), 8),\n"++
         "                  ((ForestLine False 0 0 3),\n"++
         "                   16)) NoChange [((((3,8),(3,16)),ITvarid \"putStrLn\"),\"putStrLn\")]\n"++
         "           [],\n"++
         "         Node\n"++
         "           Entry (((ForestLine False 0 0 3), 17),\n"++
         "                  ((ForestLine False 0 0 3),\n"++
         "                   24)) NoChange [((((3,17),(3,24)),ITstring \"hello\"),\"\\\"hello\\\"\")]\n"++
         "           []]]]"

  -- ---------------------------------------------

    it "allocates Tokens for a let expression" $ do
      (t,toks) <- parsedFileLetExpr
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      -- let renamed = fromJust $ GHC.tm_renamed_source t

      -- (SYB.showData SYB.Parser 0 parsed) `shouldBe` ""
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      (GHC.showRichTokenStream toks) `shouldBe` "-- A simple let expression, to ensure the layout is detected\n\n module Layout.LetExpr where\n\n foo = let x = 1\n           y = 2\n       in x + y\n\n "

      let layout = allocTokens parsed toks
      (show $ retrieveTokens layout) `shouldBe` (show toks)
      (invariant layout) `shouldBe` []
{-
      (drawTreeCompact layout) `shouldBe`
         "0:((1,1),(9,1))\n"++
         "1:((1,1),(3,7))\n"++
         "1:((3,8),(3,22))\n"++
         "1:((3,23),(3,28))\n"++
         "1:((5,1),(7,15))\n"++
         "2:((5,1),(5,4))\n"++
         "2:((5,5),(7,15))\n"++
         "3:((5,5),(5,6))\n"++
         "3:((5,7),(7,15))\n"++
         "4:((5,7),(5,10))\n"++
         "4:((5,11),(6,16))(Above None (5,11) (6,16) FromAlignCol (1,-9))\n"++
         "5:((5,11),(5,16))\n"++
         "6:((5,11),(5,12))\n"++
         "6:((5,13),(5,16))\n"++
         "7:((5,13),(5,14))\n"++
         "7:((5,15),(5,16))\n"++
         "5:((6,11),(6,16))\n"++
         "6:((6,11),(6,12))\n"++
         "6:((6,13),(6,16))\n"++
         "7:((6,13),(6,14))\n"++
         "7:((6,15),(6,16))\n"++
         "4:((7,10),(7,15))\n"++
         "5:((7,10),(7,11))\n"++
         "5:((7,12),(7,13))\n"++
         "5:((7,14),(7,15))\n"++
         "1:((9,1),(9,1))\n"
-}
      (drawTreeCompact layout) `shouldBe`
         "0:((3,1),(9,1))\n"++
         "1:((3,1),(3,7))\n"++
         "1:((3,8),(3,22))\n"++
         "1:((3,23),(3,28))\n"++
         "1:((5,1),(7,15))\n"++
         "2:((5,1),(5,4))\n"++
         "2:((5,5),(7,15))\n"++
         "3:((5,5),(5,6))\n"++
         "3:((5,7),(7,15))\n"++
         "4:((5,7),(5,10))\n"++
         "4:((5,11),(6,16))(Above None (5,11) (6,16) FromAlignCol (1,-9))\n"++
         "5:((5,11),(5,16))\n"++
         "6:((5,11),(5,12))\n"++
         "6:((5,13),(5,16))\n"++
         "7:((5,13),(5,14))\n"++
         "7:((5,15),(5,16))\n"++
         "5:((6,11),(6,16))\n"++
         "6:((6,11),(6,12))\n"++
         "6:((6,13),(6,16))\n"++
         "7:((6,13),(6,14))\n"++
         "7:((6,15),(6,16))\n"++
         "4:((7,10),(7,15))\n"++
         "5:((7,10),(7,11))\n"++
         "5:((7,12),(7,13))\n"++
         "5:((7,14),(7,15))\n"++
         "1:((9,1),(9,1))\n"

  -- ---------------------------------------------

    it "allocates Tokens for a let statement" $ do
      (t,toks) <- parsedFileLetStmt
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      -- let renamed = fromJust $ GHC.tm_renamed_source t

      -- (SYB.showData SYB.Parser 0 parsed) `shouldBe` ""
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      (GHC.showRichTokenStream toks) `shouldBe` "-- A simple let statement, to ensure the layout is detected\n\n module Layout.LetStmt where\n\n foo = do\n         let x = 1\n             y = 2\n         x+y\n\n "

      let layout = allocTokens parsed toks
      (show $ retrieveTokens layout) `shouldBe` (show toks)
      (invariant layout) `shouldBe` []

{-
      (drawTreeCompact layout) `shouldBe`
         "0:((3,1),(10,1))\n"++
         "1:((3,1),(3,7))\n"++
         "1:((3,8),(3,22))\n"++
         "1:((3,23),(3,28))\n"++
         "1:((5,1),(8,12))\n"++
         "2:((5,1),(5,4))\n"++
         "2:((5,5),(8,12))\n"++
         "3:((5,5),(5,6))\n"++
         "3:((5,7),(8,12))\n"++
         "4:((5,7),(5,9))\n"++
         "4:((6,9),(8,12))(Above FromAlignCol (1,-1) (6,9) (8,12) FromAlignCol (2,-11))\n"++
         "5:((6,9),(7,18))\n"++
         "6:((6,9),(6,12))\n"++
         "6:((6,13),(7,18))(Above None (6,13) (7,18) FromAlignCol (1,-9))\n"++
         "7:((6,13),(6,18))\n"++
         "8:((6,13),(6,14))\n"++
         "8:((6,15),(6,18))\n"++
         "9:((6,15),(6,16))\n"++
         "9:((6,17),(6,18))\n"++
         "7:((7,13),(7,18))\n"++
         "8:((7,13),(7,14))\n"++
         "8:((7,15),(7,18))\n"++
         "9:((7,15),(7,16))\n"++
         "9:((7,17),(7,18))\n"++
         "5:((8,9),(8,12))\n"++
         "6:((8,9),(8,10))\n"++
         "6:((8,10),(8,11))\n"++
         "6:((8,11),(8,12))\n"++
         "1:((10,1),(10,1))\n"
-}

  -- ---------------------------------------------

    it "allocates Tokens for a case expression" $ do
      (t,toks) <- parsedFileCaseExpr
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      -- let renamed = fromJust $ GHC.tm_renamed_source t

      -- (SYB.showData SYB.Parser 0 parsed) `shouldBe` ""
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      (GHC.showRichTokenStream toks) `shouldBe` "-- A simple case expression, to ensure the layout is detected\n\n module Layout.CaseExpr where\n\n foo x = case x of\n    1 -> \"a\"\n    2 -> \"b\"\n\n "

      let layout = allocTokens parsed toks
      (show $ retrieveTokens layout) `shouldBe` (show toks)
      (invariant layout) `shouldBe` []

{-
      (drawTreeCompact layout) `shouldBe`
         "0:((3,1),(9,1))\n"++
         "1:((3,1),(3,7))\n"++
         "1:((3,8),(3,23))\n"++
         "1:((3,24),(3,29))\n"++
         "1:((5,1),(7,12))\n"++
         "2:((5,1),(5,4))\n"++
         "2:((5,5),(7,12))\n"++
         "3:((5,5),(5,6))\n"++
         "3:((5,7),(5,8))\n"++
         "3:((5,9),(7,12))\n"++
         "4:((5,9),(5,13))\n"++
         "4:((5,14),(5,15))\n"++
         "4:((5,16),(5,18))\n"++
         "4:((6,4),(7,12))(Above FromAlignCol (1,-15) (6,4) (7,12) FromAlignCol (2,-11))\n"++
         "5:((6,4),(6,12))\n"++
         "6:((6,4),(6,5))\n"++
         "6:((6,6),(6,8))\n"++
         "6:((6,9),(6,12))\n"++
         "5:((7,4),(7,12))\n"++
         "6:((7,4),(7,5))\n"++
         "6:((7,6),(7,8))\n"++
         "6:((7,9),(7,12))\n"++
         "1:((9,1),(9,1))\n"
-}

-- ---------------------------------------------------------------------

parsedFileBare :: IO (ParseResult,[PosToken])
parsedFileBare = parsedFileGhc "./test/testdata/Layout/Bare.hs"

-- ---------------------------------------------------------------------

parsedFileLetExpr :: IO (ParseResult,[PosToken])
parsedFileLetExpr = parsedFileGhc "./test/testdata/Layout/LetExpr.hs"

-- ---------------------------------------------------------------------

parsedFileLetStmt :: IO (ParseResult,[PosToken])
parsedFileLetStmt = parsedFileGhc "./test/testdata/Layout/LetStmt.hs"

-- ---------------------------------------------------------------------

parsedFileCaseExpr :: IO (ParseResult,[PosToken])
parsedFileCaseExpr = parsedFileGhc "./test/testdata/Layout/CaseExpr.hs"

-- ---------------------------------------------------------------------
