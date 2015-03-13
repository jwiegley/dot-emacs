module Util.Cabal ( prettyVersion
                  , prettyPkgInfo
                  , parseVersion
                  , parsePkgInfo
                  , executableMatchesCabal
                  ) where

import Distribution.Version (Version(..), withinRange)
import Distribution.Package (PackageName(..), Dependency(..), PackageIdentifier(..))
import Distribution.Compat.ReadP (readP_to_S)
import Distribution.Text (parse, Text)
import Distribution.PackageDescription (condTreeConstraints, condExecutables, GenericPackageDescription)

import Data.Char (isSpace)
import Data.List (isPrefixOf, intercalate)

-- render Version to human and ghc-pkg readable string
prettyVersion :: Version -> String
prettyVersion (Version [] _) = ""
prettyVersion (Version numbers _) = intercalate "." $ map show numbers

-- render PackageIdentifier to human and ghc-pkg readable string
prettyPkgInfo :: PackageIdentifier -> String
prettyPkgInfo (PackageIdentifier (PackageName name) (Version [] _)) = name
prettyPkgInfo (PackageIdentifier (PackageName name) version) =
  name ++ "-" ++ prettyVersion version

parseVersion :: String -> Maybe Version
parseVersion = parseCheck

parseCheck :: Text a => String -> Maybe a
parseCheck str =
  case [ x | (x,ys) <- readP_to_S parse str, all isSpace ys ] of
    [x] -> Just x
    _   -> Nothing

parsePkgInfo :: String -> Maybe PackageIdentifier
parsePkgInfo str | "builtin_" `isPrefixOf` str =
                     let name = drop (length "builtin_") str -- ghc-pkg doesn't like builtin_ prefix
                     in Just $ PackageIdentifier (PackageName name) $ Version [] []
                 | otherwise = parseCheck str

executableMatchesCabal :: String -> Version -> GenericPackageDescription -> Bool
executableMatchesCabal executable cabalVersion pkgDescr =
    case lookup executable $ condExecutables pkgDescr of
      Nothing -> False
      Just depGraph ->
          let deps = condTreeConstraints depGraph
              isCabalDep (Dependency (PackageName name) _) = name == "Cabal"
              cabalDeps = filter isCabalDep deps
              matchesDep (Dependency _ versionRange) = cabalVersion `withinRange` versionRange
          in all matchesDep cabalDeps
