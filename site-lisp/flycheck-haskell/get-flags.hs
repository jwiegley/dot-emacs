-- Copyright (C) 2015 Michael Alan Dorman <mdorman@ironicdesign.com>

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

{-# LANGUAGE CPP #-}

module Main (main) where

#if __GLASGOW_HASKELL__ >= 800
#define Cabal2 MIN_VERSION_Cabal(2,0,0)
#else
-- Hack - we may actually be using Cabal 2.0 with e.g. 7.8 GHC. But
-- that's not likely to occur for average user who's relying on
-- packages bundled with GHC. The 2.0 Cabal is bundled starting with 8.2.1.
#define Cabal2 0
#endif

import Data.Version (Version (Version))
import Distribution.Simple.Utils (cabalVersion)
import System.Environment (getArgs)

#if Cabal2
import qualified Distribution.Version as CabalVersion
#endif

data Mode
  = GHC
  | HLint

define :: Mode -> String -> String
define GHC def = "-D" ++ def
define HLint def = "--cpp-define=" ++ def

legacyFlags :: Mode -> [String]
legacyFlags mode = [define mode "USE_COMPILER_ID"]

isLegacyCabal :: Bool
isLegacyCabal = cabalVersion < targetVersion
  where
    targetVersion =
#if Cabal2
        CabalVersion.mkVersion' $
#endif
        Version [1, 22] []

getMode :: [String] -> Mode
getMode ("hlint":_) = HLint
getMode _ = GHC

main :: IO ()
main = do
    args <- getArgs
    mapM_ putStrLn (flags (getMode args))
  where
    flags mode =
        if isLegacyCabal
            then legacyFlags mode
            else []
