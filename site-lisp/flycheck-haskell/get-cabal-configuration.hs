-- Copyright (C) 2014-2016 Sebastian Wiesner <swiesner@lunaryorn.com>
-- Copyright (C) 2016 Danny Navarro
-- Copyright (C) 2015 Mark Karpov <markkarpov@opmbx.org>
-- Copyright (C) 2015 Michael Alan Dorman <mdorman@ironicdesign.com>
-- Copyright (C) 2014 Gracjan Polak <gracjanpolak@gmail.com>

-- This file is not part of GNU Emacs.

-- This program is free software; you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.

-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.

-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main (main) where

#if __GLASGOW_HASKELL__ >= 800
#define Cabal2 MIN_VERSION_Cabal(2,0,0)
#else
-- Hack - we may actually be using Cabal 2.0 with e.g. 7.8 GHC. But
-- that's not likely to occur for average user who's relying on
-- packages bundled with GHC. The 2.0 Cabal is bundled starting with 8.2.1.
#define Cabal2 0
#endif

import qualified Control.Applicative as A
import Control.Exception (SomeException, try)
import Data.Char (isSpace)
import Data.List (isPrefixOf, nub)
import Data.Maybe (listToMaybe)
import Data.Set (Set)
import qualified Data.Set as S
#ifdef USE_COMPILER_ID
import Distribution.Compiler
       (CompilerFlavor(GHC), CompilerId(CompilerId), buildCompilerFlavor)
#else
import Distribution.Compiler
       (AbiTag(NoAbiTag), CompilerFlavor(GHC), CompilerId(CompilerId),
        CompilerInfo, buildCompilerFlavor, unknownCompilerInfo)
#endif
import Distribution.Package
       (pkgName, Dependency(..))
import Distribution.PackageDescription
       (GenericPackageDescription,
        PackageDescription(..), allBuildInfo, BuildInfo(..),
        usedExtensions, allLanguages, hcOptions, exeName,
        Executable)
import Distribution.Simple.BuildPaths (defaultDistPref)
import Distribution.Simple.Utils (cabalVersion)
import Distribution.System (buildPlatform)
import Distribution.Text (display)
import Distribution.Verbosity (silent)
import Language.Haskell.Extension (Extension(..),Language(..))
import System.Environment (getArgs)
import System.Exit (ExitCode(..), exitFailure)
import System.FilePath ((</>),dropFileName,normalise)
import System.Info (compilerVersion)
import System.Process (readProcessWithExitCode)

#if __GLASGOW_HASKELL__ >= 710 && !Cabal2
import Data.Version (Version)
#endif

#if Cabal2
import Distribution.Package (unPackageName, depPkgName, PackageName)
import Distribution.PackageDescription.Configuration (finalizePD)
import Distribution.Types.ComponentRequestedSpec (ComponentRequestedSpec(..))
import Distribution.PackageDescription.Parse (readGenericPackageDescription)
import Distribution.Types.UnqualComponentName (unUnqualComponentName)
import qualified Distribution.Version as CabalVersion
#else
import Control.Arrow (second)
import Data.Version (showVersion)
import Distribution.Package (PackageName(..))
import Distribution.PackageDescription
       (TestSuite, Benchmark, condTestSuites, condBenchmarks,
        benchmarkEnabled, testEnabled)
import Distribution.PackageDescription.Configuration
       (finalizePackageDescription, mapTreeData)
import Distribution.PackageDescription.Parse (readPackageDescription)
#endif

data Sexp
    = SList [Sexp]
    | SString String
    | SSymbol String

data TargetTool = Cabal | Stack

sym :: String -> Sexp
sym = SSymbol

instance Show Sexp where
    show (SSymbol s) = s
    show (SString s) = show s     -- Poor man's escaping
    show (SList s) = "(" ++ unwords (map show s) ++ ")"

class ToSexp a  where
    toSexp :: a -> Sexp

instance ToSexp String where
    toSexp = SString

instance ToSexp Extension where
    toSexp (EnableExtension ext) = toSexp (show ext)
    toSexp (DisableExtension ext) = toSexp ("No" ++ show ext)
    toSexp (UnknownExtension ext) = toSexp ext

instance ToSexp Language where
    toSexp (UnknownLanguage lang) = toSexp lang
    toSexp lang = toSexp (show lang)

instance ToSexp Dependency where
#if Cabal2
    toSexp = toSexp . unPackageName . depPkgName
#else
    toSexp (Dependency (PackageName dependency) _) = toSexp dependency
#endif

instance ToSexp Sexp where
    toSexp = id

cons :: (ToSexp a, ToSexp b) => a -> [b] -> Sexp
cons h t = SList (toSexp h : map toSexp t)

-- | Get possible dist directory
distDir :: TargetTool -> IO FilePath
distDir Cabal = return defaultDistPref
distDir Stack = do
    res <- try $ readProcessWithExitCode "stack" ["path", "--dist-dir"] []
    return $ case res of
        Left (_ :: SomeException)      -> defaultDistDir
        Right (ExitSuccess, stdOut, _) -> stripWhitespace stdOut
        Right (ExitFailure _, _, _)    -> defaultDistDir
  where
    defaultDistDir :: FilePath
    defaultDistDir =
        ".stack-work" </> defaultDistPref
                      </> display buildPlatform
                      </> "Cabal-" ++ cabalVersion'

getBuildDirectories
    :: TargetTool
    -> PackageDescription
    -> FilePath
    -> IO ([FilePath], FilePath)
getBuildDirectories tool pkgDesc cabalDir = do
    distDir' <- distDir tool
    let buildDir :: FilePath
        buildDir   = cabalDir </> distDir' </> "build"
        autogenDir :: FilePath
        autogenDir = buildDir </> "autogen"
        executableBuildDir :: Executable -> FilePath
        executableBuildDir e = buildDir </> getExeName e </> (getExeName e ++ "-tmp")
        buildDirs :: [FilePath]
        buildDirs = autogenDir : map executableBuildDir (executables pkgDesc)

        buildDirs' = case library pkgDesc of
            Just _  -> buildDir : buildDirs
            Nothing -> buildDirs
    return (buildDirs', autogenDir)

getSourceDirectories :: [BuildInfo] -> FilePath -> [String]
getSourceDirectories buildInfo cabalDir =
    map (cabalDir </>) (concatMap hsSourceDirs buildInfo)

allowedOptions :: Set String
allowedOptions = S.fromList
    [ "-W"
    , "-w"
    , "-Wall"
    , "-fglasgow-exts"
    , "-fpackage-trust"
    , "-fhelpful-errors"
    , "-F"
    , "-cpp"]

allowedOptionPrefixes :: [String]
allowedOptionPrefixes =
    [ "-fwarn-"
    , "-fno-warn-"
    , "-fcontext-stack="
    , "-firrefutable-tuples"
    , "-D"
    , "-U"
    , "-I"
    , "-fplugin="
    , "-fplugin-opt="
    , "-pgm"
    , "-opt"]

isAllowedOption :: String -> Bool
isAllowedOption opt =
    S.member opt allowedOptions || any (`isPrefixOf` opt) allowedOptionPrefixes

dumpPackageDescription :: PackageDescription -> FilePath -> IO Sexp
dumpPackageDescription pkgDesc cabalFile = do
    (cabalDirs, autogenDir)  <- getBuildDirectories Cabal pkgDesc cabalDir
    (stackDirs, autogenDir') <- getBuildDirectories Stack pkgDesc cabalDir
    let buildDirs   = cabalDirs ++ stackDirs
        autogenDirs = [autogenDir, autogenDir']
    return $
        SList
            [ cons (sym "build-directories") (ordNub (map normalise buildDirs))
            , cons (sym "source-directories") sourceDirs
            , cons (sym "extensions") exts
            , cons (sym "languages") langs
            , cons (sym "dependencies") deps
            , cons (sym "other-options") (cppOpts ++ ghcOpts)
            , cons (sym "autogen-directories") (map normalise autogenDirs)
            ]
  where
    cabalDir :: FilePath
    cabalDir = dropFileName cabalFile
    buildInfo :: [BuildInfo]
    buildInfo = allBuildInfo pkgDesc
    sourceDirs :: [FilePath]
    sourceDirs = ordNub (map normalise (getSourceDirectories buildInfo cabalDir))
    exts :: [Extension]
    exts = nub (concatMap usedExtensions buildInfo)
    langs :: [Language]
    langs = nub (concatMap allLanguages buildInfo)
    thisPackage :: PackageName
    thisPackage = pkgName (package pkgDesc)
    deps :: [Dependency]
    deps =
        nub (filter (\(Dependency name _) -> name /= thisPackage) (buildDepends pkgDesc))
    -- The "cpp-options" configuration field.
    cppOpts :: [String]
    cppOpts =
        ordNub (filter isAllowedOption (concatMap cppOptions buildInfo))
    -- The "ghc-options" configuration field.
    ghcOpts :: [String]
    ghcOpts =
        ordNub (filter isAllowedOption (concatMap (hcOptions GHC) buildInfo))

dumpCabalConfiguration :: FilePath -> IO ()
dumpCabalConfiguration cabalFile = do
    genericDesc <-
#if Cabal2
        readGenericPackageDescription silent cabalFile
#else
        readPackageDescription silent cabalFile
#endif
    case getConcretePackageDescription genericDesc of
        Left e        -> putStrLn $ "Issue with package configuration\n" ++ show e
        Right pkgDesc -> print =<< dumpPackageDescription pkgDesc cabalFile

getConcretePackageDescription
    :: GenericPackageDescription
    -> Either [Dependency] PackageDescription
getConcretePackageDescription genericDesc = do
#if Cabal2
    let enabled :: ComponentRequestedSpec
        enabled = ComponentRequestedSpec
            { testsRequested      = True
            , benchmarksRequested = True
            }
    fst A.<$> finalizePD
        []           -- Flag assignment
        enabled      -- Enable all components
        (const True) -- Whether given dependency is available
        buildPlatform
        buildCompilerId
        []           -- Additional constraints
        genericDesc
#else
    -- This let block is eerily like one in Cabal.Distribution.Simple.Configure
    let enableTest :: TestSuite -> TestSuite
        enableTest t = t { testEnabled = True }
        enableBenchmark :: Benchmark -> Benchmark
        enableBenchmark bm = bm { benchmarkEnabled = True }
        flaggedTests =
            map (second (mapTreeData enableTest)) (condTestSuites genericDesc)
        flaggedBenchmarks =
            map
                (second (mapTreeData enableBenchmark))
                (condBenchmarks genericDesc)
        genericDesc' =
            genericDesc
            { condTestSuites = flaggedTests
            , condBenchmarks = flaggedBenchmarks
            }
    fst A.<$> finalizePackageDescription
        []
        (const True)
        buildPlatform
        buildCompilerId
        []
        genericDesc'
#endif


#ifdef USE_COMPILER_ID
buildCompilerId :: CompilerId
buildCompilerId = CompilerId buildCompilerFlavor compilerVersion
#else
buildCompilerId :: CompilerInfo
buildCompilerId = unknownCompilerInfo compId NoAbiTag
  where
    compId :: CompilerId
    compId = CompilerId buildCompilerFlavor compVersion
# if Cabal2
    compVersion :: CabalVersion.Version
    compVersion = CabalVersion.mkVersion' compilerVersion
# else
    compVersion :: Version
    compVersion = compilerVersion
# endif
#endif

getExeName :: Executable -> FilePath
getExeName =
#if Cabal2
    unUnqualComponentName . exeName
#else
    exeName
#endif

-- Textual representation of cabal version
cabalVersion' :: String
cabalVersion' =
#if Cabal2
    CabalVersion.showVersion cabalVersion
#else
    showVersion cabalVersion
#endif

ordNub :: forall a. Ord a => [a] -> [a]
ordNub = go S.empty
  where
    go :: Set a -> [a] -> [a]
    go _   []     = []
    go acc (x:xs)
        | S.member x acc = go acc xs
        | otherwise      = x : go (S.insert x acc) xs

stripWhitespace :: String -> String
stripWhitespace = reverse . dropWhile isSpace . reverse . dropWhile isSpace

main :: IO ()
main = do
    args <- getArgs
    let cabalFile = listToMaybe args
    maybe exitFailure dumpCabalConfiguration cabalFile
