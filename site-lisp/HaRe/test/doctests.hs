module Main where

import Data.List
import Language.Haskell.GhcMod
import Language.Haskell.GhcMod.Internal
import Test.DocTest


main :: IO ()
main = do
  cradle <- findCradle
  case cradleCabalFile cradle of
    Nothing -> do
      putStrLn "cabal file not found"
    Just cabalFile -> do
       pkgDesc <- parseCabalFile cabalFile
       (libs,_exes,_tests,_benches) <- cabalAllTargets pkgDesc
       opts <- getCompilerOptions [] cradle pkgDesc
       let
         docTestOpts = ghcOptions opts
                     ++ mkIncludeOpts (includeDirs opts)
                     ++ mkPkgOpts (depPackages opts)
                     ++ filter (\l -> not (isPrefixOf "Paths_" l)) libs
       -- putStrLn $ "final opts" ++ show docTestOpts
       doctest docTestOpts

  return ()

mkIncludeOpts :: [String] -> [String]
mkIncludeOpts dirs = map (\s -> "-i" ++ s) dirs

mkPkgOpts :: [(String, String, String)] -> [String]
mkPkgOpts pkgs
 = ["-hide-all-packages"]
   ++ map (\(pkg,version,hash) -> "-package-id " ++ (intercalate "-" [pkg,version,hash])) pkgs


