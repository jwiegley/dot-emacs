{-# LANGUAGE Arrows, CPP #-}

module Args (getArgs) where

import Control.Arrow
import Data.Char
import Util.Args
import System.Directory (getCurrentDirectory)
import Types

#ifdef cabal
import Util.Cabal (prettyVersion)
import Paths_hsenv (version)

versionString :: String
versionString = prettyVersion version
#else
versionString :: String
versionString = "dev"
#endif

verbosityOpt, veryVerbosityOpt, skipSanityOpt, sharingOpt, noPS1Opt, bootstrapCabalOpt :: Switch

verbosityOpt = Switch { switchName  = "verbose"
                      , switchHelp  = "Print some debugging info"
                      , switchShort = Just 'v'
                      }

veryVerbosityOpt = Switch { switchName  = "very-verbose"
                          , switchHelp  = "Print some more debugging info"
                          , switchShort = Nothing
                          }

skipSanityOpt = Switch { switchName  = "skip-sanity-check"
                       , switchHelp  = "Skip all the sanity checks (use at your own risk)"
                       , switchShort = Nothing
                       }

sharingOpt = Switch { switchName  = "dont-share-cabal-cache"
                    , switchHelp  = "Don't share ~/.cabal/packages (hackage download cache)"
                    , switchShort = Nothing
                    }

noPS1Opt =
    Switch { switchName = "no-ps1-indicator"
           , switchHelp =
               "Don't modify the shell prompt to indicate the current hsenv"
           , switchShort = Nothing
           }

bootstrapCabalOpt =
    Switch { switchName  = "bootstrap-cabal"
           , switchHelp  = "Bootstrap cabal-install inside virtual environment"
                           ++ "(Use this if you don't have cabal-install installed "
                           ++ "or it's not on your $PATH)"
           , switchShort = Nothing
           }

parentOpt, nameOpt, ghcOpt :: DynOpt

parentOpt = DynOpt
            { dynOptName = "parent-dir"
            , dynOptTemplate = "PATH"
            , dynOptDescription = "current directory"
            , dynOptHelp = "Create Virtual Haskell Environment inside PATH"
            }

nameOpt = DynOpt
          { dynOptName = "name"
          , dynOptTemplate = "NAME"
          , dynOptDescription = "current directory name"
          , dynOptHelp = "Use NAME as name of the Virtual Haskell Environment"
          }

ghcOpt = DynOpt
         { dynOptName = "ghc"
         , dynOptTemplate = "VERSION|URL|FILE"
         , dynOptDescription = "system's copy of GHC"
         , dynOptHelp =
             "Use GHC from provided location -- a GHC version number, an HTTP or HTTPS URL or a path to a tarball (e.g. ghc-7.0.4-i386-unknown-linux.tar.bz2)"
         }

makeOpt :: StaticOpt
makeOpt = StaticOpt
          { staticOptName = "make-cmd"
          , staticOptTemplate = "CMD"
          , staticOptDefault = "make"
          , staticOptHelp =
              "Used as make substitute for installing GHC from tarball (e.g. gmake)"
          }

argParser :: ArgArrow () Options
argParser = proc () -> do
  verbosityFlag <- getOpt verbosityOpt -< ()
  verbosityFlag2 <- getOpt veryVerbosityOpt -< ()
  let verboseness = case (verbosityFlag, verbosityFlag2) of
                      (_, True)      -> VeryVerbose
                      (True, False)  -> Verbose
                      (False, False) -> Quiet
  name <- getOpt nameOpt -< ()
  parentFlag <- getOpt parentOpt -< ()
  parent <- case parentFlag of
           Just parent' -> returnA -< parent'
           Nothing -> liftIO' getCurrentDirectory -< ()
  ghcFlag <- getOpt ghcOpt -< ()
  noPS1' <- getOpt noPS1Opt -< ()
  let ghc = case ghcFlag of
              Nothing   -> System
              -- First check for URLs (@//@ is not meaningful in Posix file
              -- paths), then versions and then default to path.
              Just s | "https://" == take 8 s -> Url s
                     | "http://"  == take 7 s -> Url s
                     | isVersion s            -> Release s
                     | otherwise              -> Tarball s
  skipSanityCheckFlag <- getOpt skipSanityOpt -< ()
  noSharingFlag <- getOpt sharingOpt -< ()
  bootstrapCabalFlag <- getOpt bootstrapCabalOpt -< ()
  make <- getOpt makeOpt -< ()
  returnA -< Options{ verbosity       = verboseness
                   , skipSanityCheck = skipSanityCheckFlag
                   , envParentDir    = parent
                   , hsEnvName       = name
                   , ghcSource       = ghc
                   , makeCmd         = make
                   , noSharing       = noSharingFlag
                   , noPS1           = noPS1'
                   , cabalBootstrap  = bootstrapCabalFlag
                   }
    where liftIO' = liftIO . const

getArgs :: IO Options
getArgs = parseArgs argParser versionString outro
  where
    outro = "Creates Virtual Haskell Environment in the current directory.\n"
         ++ "All files will be stored in the .hsenv[_NAME]/ subdirectory.\n"
         ++ "\n"
         ++ "To activate a sandbox in the current directory, run:\n"
         ++ "\n"
         ++ "    source .hsenv/bin/activate\n"
         ++ "\n"
         ++ "To deactivate an active sandbox, run:\n"
         ++ "\n"
         ++ "    deactivate_hsenv"

isVersion :: String -> Bool
isVersion s = case dropWhile isDigit s of
                ""     -> s /= ""
                '.':s' -> s /= '.':s' && isVersion s'
                _      -> False
