module TokenUtilsSpec (main, spec) where

import           Test.Hspec

-- import qualified FastString as GHC
import qualified GHC        as GHC
-- import qualified Lexer      as GHC

import qualified GHC.SYB.Utils as SYB

import Data.Maybe

import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils

import qualified Data.Map as Map

import Language.Haskell.TokenUtils.DualTree
import Language.Haskell.TokenUtils.GHC.Layout
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

  describe "syncAST" $ do
    it "updates an AST and a tree to have the same SrcSpan structure" $ do
      (t,toks) <- parsedFileTokenTestGhc
      let forest = mkTreeFromTokens toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let decl@(GHC.L l _) = head $ drop 1 decls
      (showGhc l) `shouldBe` "test/testdata/TokenTest.hs:(13,1)-(15,16)"
      (showSrcSpan l) `shouldBe` "((13,1),(15,17))"

      let (forest',tree) = getSrcSpanFor forest (gs2f l)

      let toks' = retrieveTokensInterim tree
      let (forest'',sspan) = addNewSrcSpanAndToksAfter forest' (gs2ss l) (gs2ss l) (PlaceOffset 2 0 2) toks'
      (invariant forest'') `shouldBe` []
      (drawTreeEntry forest'') `shouldBe`
              "((1,1),(21,14))\n|\n"++
              "+- ((1,1),(10,10))\n|\n"++
              "+- ((13,1),(15,17))\n|\n"++
              "+- ((1000013,1),(1000015,17))\n|\n"++ -- our inserted span
              "`- ((19,1),(21,14))\n"
      (showSrcSpanF $ ss2gs sspan) `shouldBe` "(((False,0,1,13),1),((False,0,1,15),17))"

      let decl' = syncAST decl (ss2f sspan) --  forest''
          forest''' = forest''

      (showGhc decl') `shouldBe` "TokenTest.bab a b = let bar = 3 in b GHC.Num.+ bar"
      (take 90 $ SYB.showData SYB.Renamer 0 decl') `shouldBe` "\n(L {foo:(1048589,1)-(1048591,16)} \n (FunBind \n  (L {test/testdata/TokenTest.hs:1048589:1-"

      -- let toksFinal = retrieveTokensFinal forest'''
      (renderLinesFromLayoutTree forest''') `shouldBe` "module TokenTest where\n\n-- Test new style token manager\n\nbob a b = x\n  where x = 3\n\nbib a b = x\n  where\n    x = 3\n\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n\n\n\n"

  -- ---------------------------------------------

  describe "indentDeclToks" $ do
    it "adds a positive offset to a decl and toks" $ do
      (t,toks) <- parsedFileLayoutIn2
      let forest = mkTreeFromTokens toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      -- let decls = hsBinds renamed

      let Just decl@(GHC.L l _) = (locToExp (8,13) (12,43) renamed) :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))

      (showGhc l) `shouldBe` "test/testdata/Renaming/LayoutIn2.hs:(8,14)-(12,42)"
      (showSrcSpan l) `shouldBe` "((8,14),(12,43))"

      (showGhc decl) `shouldBe`
           "case list of {\n"++
           "  (1 : xs) -> 1\n"++
           "  (2 : xs)\n"++
           "    | x GHC.Classes.< 10 -> 4\n"++
           "    where\n"++
           "        x = GHC.List.last xs\n"++
           "  otherwise -> 12 }"
      let (GHC.L _ (GHC.HsCase expr (GHC.MatchGroup matches typ))) = decl
      (showGhc expr) `shouldBe` "list"

      let (GHC.L m1l _) = head matches
      (showSrcSpan m1l) `shouldBe` "((8,28),(8,39))"
      let (m1,forest') = indentDeclToks syncAST (head matches) forest 4

      -- let toks' = retrieveTokensInterim forest'
      (invariant forest') `shouldBe` []
      (drawTreeEntry forest') `shouldBe`
              "((10000000001,1),(10000000012,43))\n|\n"++
              "+- ((1,1),(8,26))\n|\n"++
              "+- ((8,32),(8,43))\n|\n"++ -- Indented by 4
              "`- ((10,28),(12,43))\n"

      -- let toksFinal = retrieveTokensFinal forest'
      (renderLinesFromLayoutTree forest') `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly list = case list of      (1:xs) -> 1\n--There is a comment\n                           (2:xs)\n                             | x < 10    -> 4  where  x = last xs\n                           otherwise -> 12\n\n"

      let decl' = (GHC.L l (GHC.HsCase expr (GHC.MatchGroup (m1:(tail matches)) typ)))
      (showGhc decl') `shouldBe` "case list of {\n  (1 : xs) -> 1\n  (2 : xs)\n    | x GHC.Classes.< 10 -> 4\n    where\n        x = GHC.List.last xs\n  otherwise -> 12 }"
      (take 320 $ SYB.showData SYB.Renamer 0 decl') `shouldBe` "\n(L {test/testdata/Renaming/LayoutIn2.hs:(8,14)-(12,42)} \n (HsCase \n  (L {test/testdata/Renaming/LayoutIn2.hs:8:19-22} \n   (HsVar {Name: list})) \n  (MatchGroup \n   [\n    (L {foo:8:32-42} \n     (Match \n      [\n       (L {test/testdata/Renaming/LayoutIn2.hs:8:32-37} \n        (ParPat \n         (L {test/testdata/Renaming/L"

    ------------------------------------

    it "adds a negative offset to a decl and toks" $ do
      (t,toks) <- parsedFileLayoutIn2
      let forest = mkTreeFromTokens toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      -- let decls = hsBinds renamed

      let Just decl@(GHC.L l _) = (locToExp (8,13) (12,43) renamed) :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))

      (showGhc l) `shouldBe` "test/testdata/Renaming/LayoutIn2.hs:(8,14)-(12,42)"
      (showSrcSpan l) `shouldBe` "((8,14),(12,43))"

      (showGhc decl) `shouldBe`
           "case list of {\n"++
           "  (1 : xs) -> 1\n"++
           "  (2 : xs)\n"++
           "    | x GHC.Classes.< 10 -> 4\n"++
           "    where\n"++
           "        x = GHC.List.last xs\n"++
           "  otherwise -> 12 }"
      let (GHC.L _ (GHC.HsCase expr (GHC.MatchGroup matches typ))) = decl
      (showGhc expr) `shouldBe` "list"

      let (GHC.L m1l _) = head matches
      (showSrcSpan m1l) `shouldBe` "((8,28),(8,39))"
      let (m1,forest') = indentDeclToks syncAST (head matches) forest (-2)

      -- let toks' = retrieveTokensInterim forest'
      (invariant forest') `shouldBe` []
      (drawTreeEntry forest') `shouldBe`
              "((10000000001,1),(10000000012,43))\n|\n"++
              "+- ((1,1),(8,26))\n|\n"++
              "+- ((8,26),(8,37))\n|\n"++ -- dedented by 2
              "`- ((10,28),(12,43))\n"

      -- let toksFinal = retrieveTokensFinal forest'
      (renderLinesFromLayoutTree forest') `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly list = case list of(1:xs) -> 1\n--There is a comment\n                           (2:xs)\n                             | x < 10    -> 4  where  x = last xs\n                           otherwise -> 12\n\n"

      let decl' = (GHC.L l (GHC.HsCase expr (GHC.MatchGroup (m1:(tail matches)) typ)))
      (showGhc decl') `shouldBe` "case list of {\n  (1 : xs) -> 1\n  (2 : xs)\n    | x GHC.Classes.< 10 -> 4\n    where\n        x = GHC.List.last xs\n  otherwise -> 12 }"
      (take 320 $ SYB.showData SYB.Renamer 0 decl') `shouldBe` "\n(L {test/testdata/Renaming/LayoutIn2.hs:(8,14)-(12,42)} \n (HsCase \n  (L {test/testdata/Renaming/LayoutIn2.hs:8:19-22} \n   (HsVar {Name: list})) \n  (MatchGroup \n   [\n    (L {foo:8:26-36} \n     (Match \n      [\n       (L {test/testdata/Renaming/LayoutIn2.hs:8:26-31} \n        (ParPat \n         (L {test/testdata/Renaming/L"

      -- Now to do it for the second item in the list
      let (GHC.L m2l _) = head $ drop 1 matches
      (showSrcSpan m2l) `shouldBe` "((10,28),(11,66))"
      let (m2,forest2) = indentDeclToks syncAST (head $ drop 1 matches) forest' (-2)

      -- (show forest2) `shouldBe` ""
      -- TODO: sort out this invariant failing
      -- (show forest) `shouldBe` "forest"
      -- (show forest') `shouldBe` "forest'"
      -- (show forest2) `shouldBe` "forest2"
      (invariant forest2) `shouldBe` []
      (drawTreeEntry forest2) `shouldBe`
              "((10000000001,1),(10000000012,43))\n|\n"++
              "+- ((1,1),(8,26))\n|\n"++
              "+- ((8,26),(8,37))\n|\n"++
              "`- ((10000000010,28),(10000000012,43))\n   |\n"++
              "   +- ((10,26),(11,64))\n   |\n"++
              "   `- ((12,28),(12,43))\n"

      -- let toksFinal2 = retrieveTokensFinal forest2
      (renderLinesFromLayoutTree forest2) `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly list = case list of(1:xs) -> 1\n--There is a comment\n                         (2:xs)\n                           | x < 10    -> 4  where  x = last xs\n                           otherwise -> 12\n\n"

      let decl2 = (GHC.L l (GHC.HsCase expr (GHC.MatchGroup (m1:m2:(tail $ tail matches)) typ)))
      (showGhc decl2) `shouldBe` "case list of {\n  (1 : xs) -> 1\n  (2 : xs)\n    | x GHC.Classes.< 10 -> 4\n    where\n        x = GHC.List.last xs\n  otherwise -> 12 }"
      (take 320 $ SYB.showData SYB.Renamer 0 decl2) `shouldBe` "\n(L {test/testdata/Renaming/LayoutIn2.hs:(8,14)-(12,42)} \n (HsCase \n  (L {test/testdata/Renaming/LayoutIn2.hs:8:19-22} \n   (HsVar {Name: list})) \n  (MatchGroup \n   [\n    (L {foo:8:26-36} \n     (Match \n      [\n       (L {test/testdata/Renaming/LayoutIn2.hs:8:26-31} \n        (ParPat \n         (L {test/testdata/Renaming/L"

  -- ---------------------------------------------

  describe "syncAstToLatestCache" $ do
    it "update the SrcSpans in a declaration to match the latest stash" $ do
      (t,toks) <- parsedFileDemoteD1
      let tk = initTokenCache toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let decl@(GHC.L l _) = head decls
      (showGhc l) `shouldBe` "test/testdata/Demote/D1.hs:11:1-7"
      (showSrcSpan l) `shouldBe` "((11,1),(11,8))"

      let tk' = removeToksFromCache tk (gs2ss l)
      (drawTokenCache tk') `shouldBe`
               "tree TId 0:\n"++
               "((1,1),(13,25))\n|\n"++
               "+- ((1,1),(9,14))\n|\n"++
               "+- ((11,1),(11,8))(2,-7)D\n|\n"++
               "`- ((13,1),(13,25))\n"++
               "tree TId 1:\n"++
               "((100000011,1),(100000011,8))\n"

      let mainForest = (tkCache tk') Map.! mainTid
      let sspan = posToSrcSpan mainForest ((11,1),(11,8))

      let sspan2 = insertForestLineInSrcSpan (ForestLine False 1 0 1) sspan
      (showGhc sspan2) `shouldBe` "f:(33554433,1)-(33554443,7)"
      (showSrcSpanF sspan2) `shouldBe` "(((False,1,0,1),1),((False,1,0,11),8))"

      let (GHC.L ss' _) = syncAstToLatestCache tk' decl
      -- (showGhc ss') `shouldBe` "f:100000011:1-7"
      (showGhc ss') `shouldBe` "foo:33554443:1-7"
      (showSrcSpanF ss') `shouldBe` "(((False,1,0,11),1),((False,1,0,11),8))"

  -- ---------------------------------------------

parsedFileTokenTestGhc :: IO (ParseResult,[PosToken])
parsedFileTokenTestGhc = parsedFileGhc "./test/testdata/TokenTest.hs"

-- ---------------------------------------------------------------------

parsedFileDemoteD1 :: IO (ParseResult, [PosToken])
parsedFileDemoteD1 = parsedFileGhc "./test/testdata/Demote/D1.hs"


parsedFileLayoutIn2 :: IO (ParseResult, [PosToken])
parsedFileLayoutIn2 = parsedFileGhc "./test/testdata/Renaming/LayoutIn2.hs"

