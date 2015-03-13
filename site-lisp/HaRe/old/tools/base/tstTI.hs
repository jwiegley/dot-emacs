{-
This is a main program for testing the type checker. You can run it like this

  tstTI [flags] file_1 ... file_n

where flags include

   -debug +debug: turn off/on verbose output
   -utf8 +utf8: turn off/on the use of unicode characters in the output

The files should contain the Haskell modules to be type checked. All modules
implicitly import the Prelude, so one of the files must contain a module
called Prelude.

Mutually recursive modules are accepted.
-}

import HsParser(parse)
import HsModule(HsModuleI(..))
import TiDecorate(TiDecls)
--import TiBase
--import ParsedSyntax(HsModuleR)
import TiHsName()
import ReAssocBase()
import ScopeNamesBase()
import NameMapsBase()
import PPU(ppu,getPPopts,ucatch)
import PrettySymbols(happy)
import PrettyPrint(($$))
import TiProgram(tcProgramFiles)
import MUtils(( # ))
import DirUtils(expand)

main =
  do (o@(u,_),_,args) <- getPPopts
     ucatch u (tstTi o =<< expand args)

tstTi o files =
  putStrLn =<< (ppu o.($$happy).r.fst # tcProgramFiles parse files)

r = id :: I [[HsModuleI i1 (TiDecls i2)]]
--r = id :: I [[HsModuleR]]
type I a = a->a
