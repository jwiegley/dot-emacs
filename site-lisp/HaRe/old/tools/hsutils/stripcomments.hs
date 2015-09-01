{-+
This is a small utility to strip blank lines and comments from Haskell files.

Haskell modules are read from files named on the command line.

The result is output on stdout.

Haskell files whose names end with ".lhs" are assumed to be in literate style.
-}

import System(getArgs)
import Unlit(readHaskellFile)
import StripComments(stripcomments)

main = mapM_ stripFile =<< getArgs

stripFile path = putStrLn . stripcomments =<< readHaskellFile path
