module MonadFunctionsSpec (main, spec) where

import           Test.Hspec

import TestUtils

import qualified GHC        as GHC

import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils

import Language.Haskell.TokenUtils.DualTree


main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do
  describe "indentDeclAndToks" $ do
    it "indents a declaration and its tokens" $ do
      (t, toks) <- parsedFileLayoutIn2
      -- let renamed = fromJust $ GHC.tm_renamed_source t

      let
        comp = do
          renamed <- getRefactRenamed
          let Just decl@(GHC.L _l _) = (locToExp (8,13) (12,43) renamed) :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))
          r <- indentDeclAndToks decl (6)

          let Just ((GHC.L _ n)) = locToName (8,1) renamed
          let [decl2] = definingDeclsNames [n] (hsBinds renamed) False False
          r2 <- indentDeclAndToks decl2 (6)

          return (r,r2,decl,decl2)
      ((res,res2,d,d2),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res,d),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc d) `shouldBe` "case list of {\n  (1 : xs) -> 1\n  (2 : xs)\n    | x GHC.Classes.< 10 -> 4\n    where\n        x = GHC.List.last xs\n  otherwise -> 12 }"
      (showGhc res) `shouldBe` "case list of {\n  (1 : xs) -> 1\n  (2 : xs)\n    | x GHC.Classes.< 10 -> 4\n    where\n        x = GHC.List.last xs\n  otherwise -> 12 }"
      (showGhc d2) `shouldBe` "LayoutIn2.silly list\n  = case list of {\n      (1 : xs) -> 1\n      (2 : xs)\n        | x GHC.Classes.< 10 -> 4\n        where\n            x = GHC.List.last xs\n      otherwise -> 12 }"
      (showGhc res2) `shouldBe` "LayoutIn2.silly list\n  = case list of {\n      (1 : xs) -> 1\n      (2 : xs)\n        | x GHC.Classes.< 10 -> 4\n        where\n            x = GHC.List.last xs\n      otherwise -> 12 }"
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\n      silly list =       case list of  (1:xs) -> 1\n            --There is a comment\n                                       (2:xs)\n                                         | x < 10    -> 4  where  x = last xs\n                                       otherwise -> 12\n\n"

    -- ---------------------------------

-- ---------------------------------------------------------------------

parsedFileLayoutIn2 :: IO (ParseResult, [PosToken])
parsedFileLayoutIn2 = parsedFileGhc "./test/testdata/Renaming/LayoutIn2.hs"

