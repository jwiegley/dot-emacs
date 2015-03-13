module CaseSpec (main, spec) where

import           Test.Hspec

import Language.Haskell.Refact.Refactoring.Case

import TestUtils

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "ifToCase" $ do
    it "converts an if expression to a case expression B" $ do
      r <- ifToCase defaultTestSettings testCradle "./test/testdata/Case/B.hs" (4,7) (4,43)
      -- r <- ifToCase logTestSettings testCradle "./test/testdata/Case/B.hs" (4,7) (4,43)
      r `shouldBe` ["./test/testdata/Case/B.hs"]
      diff <- compareFiles "./test/testdata/Case/B.refactored.hs"
                           "./test/testdata/Case/B.hs.expected"
      diff `shouldBe` []

    -- ---------------------------------

    it "converts an if expression with comments to a case expression 1 C" $ do

      r <- ifToCase defaultTestSettings testCradle "./test/testdata/Case/C.hs" (5,7) (10,1)
      -- ifToCase logTestSettings testCradle "./test/testdata/Case/C.hs" (5,7) (10,1)
      r `shouldBe` ["./test/testdata/Case/C.hs"]
      diff <- compareFiles "./test/testdata/Case/C.refactored.hs"
                           "./test/testdata/Case/C.hs.expected"
      diff `shouldBe` []

    -- ---------------------------------

    it "converts an if expression with comments to a case expression 2 D" $ do
      r <- ifToCase defaultTestSettings testCradle "./test/testdata/Case/D.hs" (5,7) (12,1)
      -- ifToCase logTestSettings testCradle "./test/testdata/Case/D.hs" (5,7) (12,1)
      r `shouldBe` ["./test/testdata/Case/D.hs"]
      diff <- compareFiles "./test/testdata/Case/D.refactored.hs"
                           "./test/testdata/Case/D.hs.expected"
      diff `shouldBe` []

    -- ---------------------------------

    it "converts in complex sub level expression 2 E" $ do
      r <- ifToCase defaultTestSettings testCradle "./test/testdata/Case/E.hs" (7,8) (13,20)
      -- ifToCase logTestSettings testCradle "./test/testdata/Case/E.hs" (7,8) (13,20)
      r `shouldBe` ["./test/testdata/Case/E.hs"]
      diff <- compareFiles "./test/testdata/Case/E.refactored.hs"
                           "./test/testdata/Case/E.hs.expected"
      diff `shouldBe` []

    -- ---------------------------------

    it "complains if an if-then-else is not selected" $ do
      res <- catchException(ifToCase defaultTestSettings testCradle "./test/testdata/Case/C.hs" (4,7) (9,1))
      -- ifToCase logTestSettings testCradle "./test/testdata/Case/C.hs" (4,7) (9,1)
      (show res) `shouldBe` "Just \"You haven't selected an if-then-else  expression!\""

-- ---------------------------------------------------------------------
-- Helper functions


