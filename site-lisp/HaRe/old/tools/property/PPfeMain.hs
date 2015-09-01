module PPfeMain where
import AbstractIO(ePutStrLn,try)
import PPU(getPPopts)
--import LexerOptions(lexerOptions,lexerflags0)
import PropLexer(pLexerPass0)
import PropParser(parse)
import SIO(runSIO,withStdio)
import PfeDepCmds(runPFE5Cmds)
import ReAssocProp() -- instance HasInfixDecls for output from parse
import PfeSocket(connectToPFE,pfeClient,clientOps)

mainPFE pfeCmds =
  do (opts,prgname,args0) <- getPPopts
     let --(lexerflags,args1) = lexerOptions lexerflags0 args0
	 args1 = args0
	 ao=(opts,prgname,args1)
	 lp=(pLexerPass0 {-lexerflags-},parse)
     r <- try (connectToPFE "hi") -- hardwired project directory path?!
     runSIO $ withStdio clientOps $
      case r of
       Left _  -> runPFE5Cmds () (pfeCmds (prgname++" [<options>]")) lp ao
       Right h -> do ePutStrLn "Using PFE server, command line options ignored."
                     pfeClient h args1


     --lexerflags1 <- fromMaybe lexerflags0 # readFileMaybe lexerflagsPath
--     lexerflags1 <- return lexerflags0 -- grr!
--   when (lexerflags/=lexerflags1) $ writeFile lexerflagsPath (show lexerflags)
--lexerflagsPath dir=dir++"lexeroptions"
