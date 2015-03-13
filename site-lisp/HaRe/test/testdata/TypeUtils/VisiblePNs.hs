{-# LANGUAGE CPP #-}
module TypeUtils.VisiblePNs where


import           Test.Hspec
-- import           Test.QuickCheck

-- import           TestUtils

-- import qualified Digraph    as GHC
-- import qualified GHC        as GHC
-- import qualified HscTypes   as GHC

-- import Control.Exception
-- import Control.Monad.State
-- import Data.Maybe
-- import Language.Haskell.GhcMod
-- import Language.Haskell.Refact.Renaming
-- import Language.Haskell.Refact.Utils
-- import Language.Haskell.Refact.Utils.GhcBugWorkArounds
-- import Language.Haskell.Refact.Utils.GhcVersionSpecific
-- import Language.Haskell.Refact.Utils.LocUtils
-- import Language.Haskell.Refact.Utils.Monad
-- import Language.Haskell.Refact.Utils.MonadFunctions
-- import Language.Haskell.Refact.Utils.TypeSyn
-- import Language.Haskell.Refact.Utils.TypeUtils
-- import System.Directory

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  describe "locToExp on ParsedSource" $ do
    it "finds the largest leftmost expression contained in a given region #1" $ do
      (t, _toks) <- parsedFileBGhc
      let modu = yy -- GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let (Just expr) = ww -- locToExp (7,7) (7,43) modu -- :: Maybe (GHC.Located (GHC.HsExpr GHC.RdrName))
      getLocatedStart expr `shouldBe` (7,9)
      getLocatedEnd   expr `shouldBe` (7,42)

    it "finds the largest leftmost expression contained in a given region #2" $ do
      -- ((_, _, mod), toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let modu = yy -- GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let (Just expr) = (Just xx) -- locToExp (7,7) (7,41) modu :: Maybe (GHC.Located (GHC.HsExpr GHC.RdrName))
      getLocatedStart expr `shouldBe` (7,12)
      getLocatedEnd   expr `shouldBe` (7,19)

  -- -------------------------------------------------------------------

  describe "getModuleGhc" $ do
    it "retrieves a module from an existing module graph" $ do
      let
        comp = do
          loadModuleGraphGhc $ Just ["./test/testdata/M.hs"]
          getModuleGhc "./test/testdata/S1.hs"
          pr <- getTypecheckedModule
          toks <- fetchOrigToks
          -- g <- clientModsAndFiles $ GHC.mkModuleName "S1"
          let g = undefined

          return ((pr,toks),g)

      (( ( (t,_)), mg ), _s) <- runRefactGhcState comp
      let parsed = zz -- GHC.pm_parsed_source $ GHC.tm_parsed_module t

      (show $ getModuleName parsed) `shouldBe` "Just (S1,\"S1\")"
      -- showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:M2, main:M3, main:Main]"

ww = undefined
xx = undefined
yy = undefined
zz = undefined
runRefactGhcState = undefined
parsedFileGhc = undefined
getTypecheckedModule = undefined
fetchOrigToks = undefined
data PosToken = PT
data ParseResult = PR
loadModuleGraphGhc = undefined
getLocatedStart = undefined
getLocatedEnd = undefined
getModuleGhc = undefined
getModuleName= undefined

-- ---------------------------------------------------------------------
-- Helper functions

-- bFileName :: GHC.FastString
-- bFileName = GHC.mkFastString "./test/testdata/TypeUtils/B.hs"

parsedFileBGhc :: IO (ParseResult,[PosToken])
parsedFileBGhc = parsedFileGhc "./test/testdata/TypeUtils/B.hs"

-- parsedFileMGhc :: IO (ParseResult,[PosToken])
-- parsedFileMGhc = parsedFileGhc "./test/testdata/M.hs"

-- ---------------------------------------------------------------------

