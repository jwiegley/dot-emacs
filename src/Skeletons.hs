{-# LANGUAGE TemplateHaskell #-}

module Skeletons where

import Data.FileEmbed (embedFile)
import Data.ByteString.Char8 (unpack)
import System.FilePath ((</>))

activateSkel :: String
activateSkel = unpack $(embedFile $ "skeletons" </> "activate")

cabalWrapperSkel :: String
cabalWrapperSkel = unpack $(embedFile $ "skeletons" </> "cabal")

cabalConfigSkel :: String
cabalConfigSkel = unpack $(embedFile $ "skeletons" </> "cabal_config")

simpleWrappers :: [(String, String)]
simpleWrappers = [ ghcWrapperSkel
                 , ghciWrapperSkel
                 , ghcPkgWrapperSkel
                 , ghcModWrapperSkel
                 , runghcWrapperSkel
                 ]

ghcWrapperSkel :: (String, String)
ghcWrapperSkel = ("ghc", unpack $(embedFile $ "skeletons" </> "ghc"))

ghciWrapperSkel :: (String, String)
ghciWrapperSkel = ("ghci", unpack $(embedFile $ "skeletons" </> "ghci"))

ghcPkgWrapperSkel :: (String, String)
ghcPkgWrapperSkel = ("ghc-pkg", unpack $(embedFile $ "skeletons" </> "ghc-pkg"))

ghcModWrapperSkel :: (String, String)
ghcModWrapperSkel = ("ghc-mod", unpack $(embedFile $ "skeletons" </> "ghc-mod"))

runghcWrapperSkel :: (String, String)
runghcWrapperSkel = ("runghc", unpack $(embedFile $ "skeletons" </> "runghc"))
