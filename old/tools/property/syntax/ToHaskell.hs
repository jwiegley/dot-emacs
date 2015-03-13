-- $Id: ToHaskell.hs,v 1.3 2002/03/25 22:40:41 hallgren Exp $

{-
   This would be more naturally an implicit parameter, but since it is used in
   a method instance of Printable, the class would need to be changed to have
   an implicit parameter, which would pollute the definition of
   PrettyPrint.hs.
-}
module ToHaskell (toHaskell) where

import CommandLine


toHaskell :: Bool
toHaskell = let (flags, _, _) = commandLine
            in
                ToHaskell `elem` flags
