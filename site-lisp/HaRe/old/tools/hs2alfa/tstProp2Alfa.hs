import TiProgram(tcProgramFiles)
import PropParser(parse)
import PropSyntax(hsModName)
import ReAssocProp()
--import ReAssoc
--import PrettyPrint
import TiPropDecorate()
import ReAssocProp()
import ScopeNamesProp()
import NameMapsProp()
import Prop2Alfa
import Hs2Alfa(modPath)
import FileConv(printModule)
import System(getArgs)
import DirUtils(expand)
--import UTF8

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
