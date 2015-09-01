import Fudgets(fudlogue)
import PfeBrowserF(mainF)
import PPU(getPPopts)
--import PFE0(maybeF)
--import LexerOptions
import PFE_Certs(getProgramaticaDir,getCertServers')

--import Maybe(fromMaybe)
--import MUtils
--import FileUtils(readFileMaybe)

main =
  do (opts,name,args0) <- getPPopts
   --lexerflags1 <- fromMaybe lexerflags0 # maybeF readFileMaybe lexerflagsPath
   --lexerflags1 <- return lexerflags0
     let --(lexerflags,args1) = lexerOptions lexerflags1 args0
         args1 = args0
     pdir <- getProgramaticaDir
     servers <- getCertServers' pdir
     fudlogue $ mainF ({-lexerflags,-}(opts,name,args1)) pdir servers

--exerflagsPath dir=dir++"lexeroptions" -- copied from ppfe.hs !!
