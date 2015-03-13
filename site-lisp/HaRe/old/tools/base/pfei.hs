import System(system)
import Monad(when)
import IO(stdout,hFlush)

import PFE
import HsParser(parse)
import Unlit(readHaskellFile)
import ParseMonad(parseFile)
import ReAssocBase()
import ScopeNamesBase()
import NameMapsBase()
import PrettyPrint
import HsModule
import HsName(ModuleName(..))

import HasIO
import CmdLineParser
import qualified AbstractIO as FU

main =
    do putStr "PFE> "
       hFlush stdout -- just because GHC is stupid
       s <- getLine
       when (s/="quit") $
         do pfe' cmds parse (words s) `catch` print
            main
  where
    cmds = pfeCmds++icmds

    icmds = [("prepp",Args "<module>" ppModule),
             ("!",Args "<shell command>" shell)]

    shell args = io $ print =<< system (unwords args)

    ppModule (arg:_) =
       do m <- preparseSourceFile =<< findFile (Module arg)
	  FU.putStrLn (pp m)
