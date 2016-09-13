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

import Data.Version (Version (Version))
import Distribution.Simple.Utils (cabalVersion)
import System.Environment (getArgs)

data Mode
  = GHC
  | HLint

define :: Mode -> String -> String
define GHC def = "-D" ++ def
define HLint def = "--cpp-define=" ++ def

legacyFlags :: Mode -> [String]
legacyFlags mode = [define mode "USE_COMPILER_ID"]

isLegacyCabal :: Bool
isLegacyCabal = cabalVersion < Version [1, 22] []

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
