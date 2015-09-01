{-# LANGUAGE CPP #-}
module UtilsSpec (main, spec) where

import           Test.Hspec
-- import           Test.QuickCheck

import           TestUtils

import qualified GHC        as GHC
import qualified HscTypes   as GHC

import Control.Exception
import Control.Monad.State
import Data.Maybe
import Language.Haskell.GhcMod
import Language.Haskell.Refact.Refactoring.Renaming
import Language.Haskell.Refact.Utils.GhcBugWorkArounds
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.Refact.Utils.Utils
import System.Directory

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  describe "locToExp on ParsedSource" $ do
    it "finds the largest leftmost expression contained in a given region #1" $ do
      (t, _toks) <- parsedFileBGhc
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let (Just expr) = locToExp (7,7) (7,43) parsed :: Maybe (GHC.Located (GHC.HsExpr GHC.RdrName))
      getLocatedStart expr `shouldBe` (7,9)
      getLocatedEnd   expr `shouldBe` (7,42)

    it "finds the largest leftmost expression contained in a given region #2" $ do
      -- ((_, _, mod), toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let modu = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let (Just expr) = locToExp (7,7) (7,41) modu :: Maybe (GHC.Located (GHC.HsExpr GHC.RdrName))
      getLocatedStart expr `shouldBe` (7,12)
      getLocatedEnd   expr `shouldBe` (7,19)

    it "finds the largest leftmost expression in RenamedSource" $ do
      -- ((_, renamed, _), toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let (Just expr) = locToExp (7,7) (7,41) renamed :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))
      getLocatedStart expr `shouldBe` (7,12)
      getLocatedEnd   expr `shouldBe` (7,19)

  describe "locToExp on RenamedSource" $ do
    it "finds the largest leftmost expression contained in a given region #1" $ do
      -- ((_, Just renamed, _), toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let (Just expr) = locToExp (7,7) (7,43) renamed :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))
      getLocatedStart expr `shouldBe` (7,9)
      getLocatedEnd   expr `shouldBe` (7,42)

  -- -------------------------------------------------------------------

  describe "loading a file" $ do
    it "loads a file having the LANGUAGE CPP pragma" $ do
      (_t, toks) <- parsedFileGhc "./test/testdata/BCpp.hs"
      -- let renamed = fromJust $ GHC.tm_renamed_source t
      -- let (Just expr) = locToExp (6,1) (12,1) renamed :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))

#if __GLASGOW_HASKELL__ > 704
      (show $ toks) `shouldBe` "[((((1,1),(1,35)),ITblockComment \" FlexibleInstances #\"),\"{-# LANGUAGE FlexibleInstances #-}\"),((((2,1),(2,21)),ITblockComment \" CPP #\"),\"{-# LANGUAGE CPP #-}\"),((((3,1),(3,53)),ITlineComment \"-- Check that we can parse a file which requires CPP\"),\"-- Check that we can parse a file which requires CPP\"),((((4,1),(4,7)),ITmodule),\"module\"),((((4,8),(4,12)),ITconid \"BCpp\"),\"BCpp\"),((((4,13),(4,18)),ITwhere),\"where\"),((((6,1),(6,1)),ITvocurly),\"\"),((((6,1),(6,4)),ITvarid \"bob\"),\"bob\"),((((6,5),(6,7)),ITdcolon),\"::\"),((((6,8),(6,11)),ITconid \"Int\"),\"Int\"),((((6,12),(6,14)),ITrarrow),\"->\"),((((6,15),(6,18)),ITconid \"Int\"),\"Int\"),((((6,19),(6,21)),ITrarrow),\"->\"),((((6,22),(6,25)),ITconid \"Int\"),\"Int\"),((((7,1),(7,29)),ITlineComment \"#if __GLASGOW_HASKELL__ > 704\"),\"#if __GLASGOW_HASKELL__ > 704\"),((((8,1),(8,1)),ITsemi),\"\"),((((8,1),(8,4)),ITvarid \"bob\"),\"bob\"),((((8,5),(8,6)),ITvarid \"x\"),\"x\"),((((8,7),(8,8)),ITvarid \"y\"),\"y\"),((((8,9),(8,10)),ITequal),\"=\"),((((8,11),(8,12)),ITvarid \"x\"),\"x\"),((((8,13),(8,14)),ITvarsym \"+\"),\"+\"),((((8,15),(8,16)),ITvarid \"y\"),\"y\"),((((9,1),(9,5)),ITlineComment \"#else\"),\"#else\"),((((10,1),(10,1)),ITlineComment \"\"),\"\"),((((10,1),(10,4)),ITlineComment \"bob\"),\"bob\"),((((10,5),(10,6)),ITlineComment \"x\"),\"x\"),((((10,7),(10,8)),ITlineComment \"y\"),\"y\"),((((10,9),(10,10)),ITlineComment \"=\"),\"=\"),((((10,11),(10,12)),ITlineComment \"x\"),\"x\"),((((10,13),(10,14)),ITlineComment \"+\"),\"+\"),((((10,15),(10,16)),ITlineComment \"y\"),\"y\"),((((10,17),(10,18)),ITlineComment \"*\"),\"*\"),((((10,19),(10,20)),ITlineComment \"2\"),\"2\"),((((11,1),(11,6)),ITlineComment \"#endif\"),\"#endif\"),((((14,1),(14,1)),ITsemi),\"\")]"
#else
      (show $ toks) `shouldBe` "[((((1,1),(1,35)),ITblockComment \" FlexibleInstances #\"),\"{-# LANGUAGE FlexibleInstances #-}\"),((((2,1),(2,21)),ITblockComment \" CPP #\"),\"{-# LANGUAGE CPP #-}\"),((((3,1),(3,53)),ITlineComment \"-- Check that we can parse a file which requires CPP\"),\"-- Check that we can parse a file which requires CPP\"),((((4,1),(4,7)),ITmodule),\"module\"),((((4,8),(4,12)),ITconid \"BCpp\"),\"BCpp\"),((((4,13),(4,18)),ITwhere),\"where\"),((((6,1),(6,1)),ITvocurly),\"\"),((((6,1),(6,4)),ITvarid \"bob\"),\"bob\"),((((6,5),(6,7)),ITdcolon),\"::\"),((((6,8),(6,11)),ITconid \"Int\"),\"Int\"),((((6,12),(6,14)),ITrarrow),\"->\"),((((6,15),(6,18)),ITconid \"Int\"),\"Int\"),((((6,19),(6,21)),ITrarrow),\"->\"),((((6,22),(6,25)),ITconid \"Int\"),\"Int\"),((((7,1),(7,29)),ITlineComment \"#if __GLASGOW_HASKELL__ > 704\"),\"#if __GLASGOW_HASKELL__ > 704\"),((((8,1),(8,1)),ITlineComment \"\"),\"\"),((((8,1),(8,4)),ITlineComment \"bob\"),\"bob\"),((((8,5),(8,6)),ITlineComment \"x\"),\"x\"),((((8,7),(8,8)),ITlineComment \"y\"),\"y\"),((((8,9),(8,10)),ITlineComment \"=\"),\"=\"),((((8,11),(8,12)),ITlineComment \"x\"),\"x\"),((((8,13),(8,14)),ITlineComment \"+\"),\"+\"),((((8,15),(8,16)),ITlineComment \"y\"),\"y\"),((((9,1),(9,5)),ITlineComment \"#else\"),\"#else\"),((((10,1),(10,1)),ITsemi),\"\"),((((10,1),(10,4)),ITvarid \"bob\"),\"bob\"),((((10,5),(10,6)),ITvarid \"x\"),\"x\"),((((10,7),(10,8)),ITvarid \"y\"),\"y\"),((((10,9),(10,10)),ITequal),\"=\"),((((10,11),(10,12)),ITvarid \"x\"),\"x\"),((((10,13),(10,14)),ITvarsym \"+\"),\"+\"),((((10,15),(10,16)),ITvarid \"y\"),\"y\"),((((10,17),(10,18)),ITstar),\"*\"),((((10,19),(10,20)),ITinteger 2),\"2\"),((((11,1),(11,6)),ITlineComment \"#endif\"),\"#endif\"),((((14,1),(14,1)),ITsemi),\"\")]"
#endif
      origStr <- readFile "./test/testdata/BCpp.hs"
      let toksStr = (GHC.showRichTokenStream $ bypassGHCBug7351 toks)
      -- (show (filter (\(c,_) -> c /= B) $ getGroupedDiff (lines toksStr) (lines origStr))) `shouldBe` "[]"
      (show $ compareStrings toksStr origStr) `shouldBe` "[]"

  -- -----------------------------------

    it "loads a series of files based on cabal1" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./test/testdata/cabal/cabal1"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal1"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""

      let settings = defaultSettings { rsetEnabledTargets = (True,True,False,False)
                                     -- , rsetVerboseLevel = Debug
                                     }

      r <- rename settings cradle "./src/Foo/Bar.hs" "baz1" (3, 1)
      -- r <- rename logTestSettings cradle "./src/Foo/Bar.hs" "baz1" (3, 1)
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe` "[\"test/testdata/cabal/cabal1/src/Foo/Bar.hs\","++
                            "\"test/testdata/cabal/cabal1/src/main.hs\"]"


  -- -----------------------------------

    it "loads a series of files based on cabal2, which has 2 exe" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./test/testdata/cabal/cabal2"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal1"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal2"

      let settings = defaultSettings { rsetEnabledTargets = (True,True,True,True)
                                     -- , rsetVerboseLevel = Debug
                                     }

      let handler = [Handler handler1]
          handler1 :: GHC.SourceError -> IO [String]
          handler1 e = do
             setCurrentDirectory currentDir
             return [show e]

      r <- catches (rename settings cradle "./src/Foo/Bar.hs" "baz1" (3, 1)) handler
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe` "[\"test/testdata/cabal/cabal2/src/Foo/Bar.hs\","++
                            "\"test/testdata/cabal/cabal2/src/main2.hs\","++
                            "\"test/testdata/cabal/cabal2/src/main1.hs\"]"

  -- -----------------------------------

    it "loads a series of files based on cabal3, which has a lib and an exe" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./test/testdata/cabal/cabal3"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal3"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal3"

      let settings = defaultSettings { rsetEnabledTargets = (True,True,True,True)
                                     -- , rsetVerboseLevel = Debug
                                     }

      let handler = [Handler handler1]
          handler1 :: GHC.SourceError -> IO [String]
          handler1 e = do
             setCurrentDirectory currentDir
             return [show e]

      r <- catches (rename settings cradle "./src/main1.hs" "baz1" (7, 1)) handler
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe` "[\"test/testdata/cabal/cabal3/src/main1.hs\"]"


  -- -----------------------------------
{- TODO: this test fails on travis, due to missing hspec-discover
    it "renames in HaRe Utils 1" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"

      let settings = defaultSettings { rsetEnabledTargets = (True,True,True,True)
                                     -- , rsetVerboseLevel = Debug
                                     }

      let handler = [Handler handler1]
          handler1 :: GHC.SourceError -> IO [String]
          handler1 e = do
             setCurrentDirectory currentDir
             return [show e]

      r <- catches (rename settings cradle "./src/Language/Haskell/Refact/Utils.hs" "clientModsAndFiles1" (473, 6)) handler
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe`
          "[\"./src/Language/Haskell/Refact/Utils.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\","++
           "\"test/UtilsSpec.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\"]"
-}

  -- -----------------------------------
{-
    it "renames in HaRe Utils 2" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"

      let settings = defaultSettings { rsetEnabledTargets = (True,True,True,True)
                                     , rsetVerboseLevel = Debug
                                     }

      let handler = [Handler handler1]
          handler1 :: GHC.SourceError -> IO [String]
          handler1 e = do
             setCurrentDirectory currentDir
             return [show e]

      r <- catches (rename settings cradle "./test/UtilsSpec.hs" "parsed" (41, 10)) handler
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe`
          "[\"./src/Language/Haskell/Refact/Utils.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\","++
           "\"test/UtilsSpec.hs\","++
           "\"./src/Language/Haskell/Refact/Renaming.hs\","++
           "\"./src/Language/Haskell/Refact/MoveDef.hs\","++
           "\"./src/Language/Haskell/Refact/DupDef.hs\"]"
-}
  -- -----------------------------------
{-
  -- This test does not work properly on Travis, missing hspec-discover
    it "renames in HaRe Utils 3" $ do

      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"

      let settings = defaultSettings { rsetEnabledTargets = (True,True,True,True)
                                     -- , rsetVerboseLevel = Debug
                                     }

      let handler = [Handler handler1]
          handler1 :: GHC.SourceError -> IO [String]
          handler1 e = do
             setCurrentDirectory currentDir
             return [show e]

      r <- catches (rename settings cradle "./test/UtilsSpec.hs" "parsed" (41, 11)) handler
      setCurrentDirectory currentDir

      r' <- mapM makeRelativeToCurrentDirectory r

      (show r') `shouldBe`
          "[\"test/UtilsSpec.hs\"]"
-}
  -- -------------------------------------------------------------------

  describe "sameOccurrence" $ do
    it "checks that a given syntax element is the same occurrence as another" $ do
      pending -- "write this test"

  -- -------------------------------------------------------------------

  describe "isVarId" $ do
    it "returns True if a string is a lexically valid variable name" $ do
      isVarId "foo" `shouldBe` True

    it "returns False if a string is not lexically valid variable name" $ do
      isVarId "Foo" `shouldBe` False


  -- -------------------------------------------------------------------

  describe "getModuleName" $ do
    it "returns a string for the module name if there is one" $ do
      -- modInfo@((_, _, mod), toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let modu = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let (Just (_modname,modNameStr)) = getModuleName modu
      -- let modNameStr = "foo"
      modNameStr `shouldBe` "TypeUtils.B"

    it "returns Nothing for the module name otherwise" $ do
      -- modInfo@((_, _, mod), toks) <- parsedFileNoMod
      (t, _toks) <- parsedFileNoMod
      let modu = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      getModuleName modu `shouldBe` Nothing

  -- -------------------------------------------------------------------

  describe "modIsExported" $ do
    it "needs a test or two" $ do
      pending  -- "write this test"

  -- -------------------------------------------------------------------

  describe "clientModsAndFiles" $ do
    it "can only be called in a live RefactGhc session" $ do
      pending  -- "write this test"

    ------------------------------------

    it "gets modules which directly or indirectly import a module #1" $ do
      -- TODO: harvest this commonality
      let
        comp = do
         (_p,_toks) <- parseFileMGhc -- Load the main file first
         g <- clientModsAndFiles $ GHC.mkModuleName "S1"
         return g
      (mg,_s) <- runRefactGhcState comp
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:M2, main:M3, main:Main]"

    ------------------------------------

    it "gets modules which directly or indirectly import a module #2" $ do
      let
        comp = do
         (_p,_toks) <- parseFileMGhc -- Load the main file first
         g <- clientModsAndFiles $ GHC.mkModuleName "M3"
         return g
      (mg,_s) <- runRefactGhcState comp
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:Main]"

    ------------------------------------

    it "gets modules which import a module in different cabal targets" $ do
      currentDir <- getCurrentDirectory
      -- currentDir `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe"
      setCurrentDirectory "./test/testdata/cabal/cabal2"
      -- d <- getCurrentDirectory
      -- d `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal1"
      cradle <- findCradle
      -- (show cradle) `shouldBe` ""
      -- (cradleCurrentDir cradle) `shouldBe` "/home/alanz/mysrc/github/alanz/HaRe/test/testdata/cabal/cabal2"

      let
        comp = do
         initGhcSession cradle (rsetImportPaths defaultSettings)
         -- initGhcSession cradle (rsetImportPaths logSettings)
         -- getModuleGhc "./src/Foo/Bar.hs" -- Load the file first
         g <- clientModsAndFiles $ GHC.mkModuleName "Foo.Bar"
         return g
      (mg,_s) <- runRefactGhcState comp
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:Main, main:Main]"

      setCurrentDirectory currentDir

  -- -------------------------------------------------------------------

  describe "serverModsAndFiles" $ do
    it "can only be called in a live RefactGhc session" $ do
      pending  -- "write this test"

    it "gets modules which are directly or indirectly imported by a module #1" $ do
      let
        comp = do
         (_p,_toks) <- parseFileMGhc -- Load the main file first
         g <- serverModsAndFiles $ GHC.mkModuleName "S1"
         return g
      (mg,_s) <- runRefactGhcState comp
      showGhc (map GHC.ms_mod mg) `shouldBe` "[]"

    it "gets modules which are directly or indirectly imported by a module #2" $ do
      let
        comp = do
         (_p,_toks) <- parseFileMGhc -- Load the main file first
         g <- serverModsAndFiles $ GHC.mkModuleName "M3"
         return g
      (mg,_s) <- runRefactGhcState comp
      showGhc (map GHC.ms_mod mg) `shouldBe` "[main:M2, main:S1]"


  -- -------------------------------------------------------------------
{-
  describe "getCurrentModuleGraph" $ do
    it "gets the module graph for the currently loaded modules" $ do
      let
        comp = do
         (_p,_toks) <- parseFileBGhc -- Load the file first
         g <- getCurrentModuleGraph
         return g
      (mg,_s) <- runRefactGhcState comp
      map (\m -> GHC.moduleNameString $ GHC.ms_mod_name m) mg `shouldBe` (["TypeUtils.B","TypeUtils.C"])
      map (\m -> show $ GHC.ml_hs_file $ GHC.ms_location m) mg `shouldBe` (["Just \"./test/testdata/TypeUtils/B.hs\""
                                                                           ,"Just \"./test/testdata/TypeUtils/C.hs\""])


    it "gets the updated graph, after a refactor" $ do
      pending -- "write this test"
-}
  -- -------------------------------------------------------------------
{-
  describe "sortCurrentModuleGraph" $ do
    it "needs a test or two" $ do
      let
        comp = do
         (_p,_toks) <- parseFileBGhc -- Load the file first
         g <- sortCurrentModuleGraph
         return g
      (mg,_s) <- runRefactGhcState comp
      (showGhc $ map (\m -> GHC.ms_mod m) (GHC.flattenSCCs mg)) `shouldBe` "[main:TypeUtils.C, main:TypeUtils.B]"
-}
  -- -------------------------------------------------------------------

  describe "getModuleGhc" $ do
    it "retrieves a module from an existing module graph" $ do
      let
        comp = do
          loadModuleGraphGhc $ Just ["./test/testdata/M.hs"]
          getModuleGhc "./test/testdata/S1.hs"
          pr <- getTypecheckedModule
          toks <- fetchOrigToks
          g <- clientModsAndFiles $ GHC.mkModuleName "S1"

          return ((pr,toks),g)

      (( ( (t,_)), mg ), _s) <- runRefactGhcState comp
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      (show $ getModuleName parsed) `shouldBe` "Just (S1,\"S1\")"
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:M2, main:M3, main:Main]"

    -- ---------------------------------

    it "loads the module and dependents if no existing module graph" $ do
      let
        comp = do
          getModuleGhc "./test/testdata/S1.hs"
          pr <- getTypecheckedModule
          toks <- fetchOrigToks
          g <- clientModsAndFiles $ GHC.mkModuleName "S1"

          return ((pr,toks),g)
      -- (( ( ((_,_,parsed),_)), mg ), _s) <- runRefactGhcState comp
      (( ( (t,_)), mg ), _s) <- runRefactGhcState comp
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      (show $ getModuleName parsed) `shouldBe` "Just (S1,\"S1\")"
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[]"

    -- ---------------------------------

    it "retrieves a module from an existing module graph #2" $ do
      let
        comp = do
          loadModuleGraphGhc $ Just ["./test/testdata/DupDef/Dd2.hs"]
          getModuleGhc "./test/testdata/DupDef/Dd1.hs"
          pr <- getTypecheckedModule
          toks <- fetchOrigToks
          g <- clientModsAndFiles $ GHC.mkModuleName "DupDef.Dd1"

          return ((pr,toks),g)
      -- (( ( ((_,_,parsed),_)), mg ), _s) <- runRefactGhcState comp
      (( ( (t,_)), mg ), _s) <- runRefactGhcState comp
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      (show $ getModuleName parsed) `shouldBe` "Just (DupDef.Dd1,\"DupDef.Dd1\")"
      showGhc (map (GHC.ms_mod . snd) mg) `shouldBe` "[main:DupDef.Dd2]"


  -- -------------------------------------------------------------------

  describe "runRefactGhc" $ do
    it "contains a State monad" $ do
      let
       comp = do
        s <- get
        (_t, _toks) <- parseSourceFileTest "./test/testdata/TypeUtils/B.hs"

        g <- GHC.getModuleGraph
        gs <- mapM GHC.showModule g
        -- GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))

        put (s {rsUniqState = 100})
        return (show gs)

      (_,s) <- runRefactGhcState comp
      (rsUniqState s) `shouldBe` 100

    it "contains the GhcT monad" $ do
      let
       comp = do
        s <- get
        (_t, _toks) <- parseSourceFileTest "./test/testdata/TypeUtils/B.hs"

        g <- GHC.getModuleGraph
        gs <- mapM GHC.showModule g
        -- GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))

        put (s {rsUniqState = 100})
        return (show gs)

      (r,_) <- runRefactGhcState comp
      r `shouldBe` ("[\"TypeUtils.B      ( test/testdata/TypeUtils/B.hs, interpreted )\""
                  ++",\"TypeUtils.C      ( test/testdata/TypeUtils/C.hs, interpreted )\"]")
      -- r `shouldBe` ("[\"TypeUtils.B      ( test/testdata/TypeUtils/B.hs, nothing )\""
      --             ++",\"TypeUtils.C      ( test/testdata/TypeUtils/C.hs, nothing )\"]")


  -- -------------------------------------------------------------------

  describe "RefactFlags" $ do
    it "puts the RefactDone flag through its paces" $ do
      let
        comp = do
          v1 <- getRefactDone
          clearRefactDone
          v2 <- getRefactDone
          setRefactDone
          v3 <- getRefactDone

          return (v1,v2,v3)
      ((v1',v2',v3'), _s) <- runRefactGhcState comp

      (show (v1',v2',v3')) `shouldBe` "(False,False,True)"


-- ---------------------------------------------------------------------
-- Helper functions

-- bFileName :: GHC.FastString
-- bFileName = GHC.mkFastString "./test/testdata/TypeUtils/B.hs"

parsedFileBGhc :: IO (ParseResult,[PosToken])
parsedFileBGhc = parsedFileGhc "./test/testdata/TypeUtils/B.hs"

-- parsedFileMGhc :: IO (ParseResult,[PosToken])
-- parsedFileMGhc = parsedFileGhc "./test/testdata/M.hs"

-- parseFileBGhc :: RefactGhc (ParseResult, [PosToken])
-- parseFileBGhc = parseSourceFileTest fileName
--   where
--     fileName = "./test/testdata/TypeUtils/B.hs"

parseFileMGhc :: RefactGhc (ParseResult, [PosToken])
parseFileMGhc = parseSourceFileTest fileName
  where
    fileName = "./test/testdata/M.hs"


parsedFileNoMod :: IO (ParseResult,[PosToken])
parsedFileNoMod = parsedFileGhc "./test/testdata/NoMod.hs"



-- ---------------------------------------------------------------------

