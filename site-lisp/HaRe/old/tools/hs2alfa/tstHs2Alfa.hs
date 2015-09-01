import HsParser(parse)
import Syntax(hsModName)
import TiDecorate()
import ReAssocBase()
import ScopeNamesBase()
import NameMapsBase()
import TiProgram(tcProgramFiles)
import Hs2Alfa(transModule,modPath)
import FileConv(printModule)
import System(getArgs)
--import MUtils
--import TextFileConv(toFile)
--import UTF8
import DirUtils(expand)

main =
    writeProgram . transProgram =<< tcProgram =<< expand =<< getArgs
  where
    writeProgram = mapM writeModule
    writeModule (n,m) =
        do putStrLn path
           writeFile path ( {-toFile $-}prefix++printModule m)
      where path=modPath n

    tcProgram files = tcProgramFiles parse files

    transProgram (mss,env) = map transModule' (concat mss)
      where
        transModule' m = (hsModName m,transModule (m,[]) (undefined,env))

    prefix =
      unlines [
	magic,
	"",
	"--#include \"Haskell.alfa\"",
        "{-# Alfa hiding on #-}"]

    magic = "-- Automatically converted from Haskell by hs2alfa..."
