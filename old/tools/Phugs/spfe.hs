
import PPU(getPPopts)
import LexerOptions(lexerOptions,lexerflags0)

import PropParser(parse)
import PropLexer(pLexerPass0)
--import DefinedNamesProp()
import FreeNamesProp()
import ScopeNamesProp()
import NameMapsProp()
import ReAssocProp()
import MapDeclMProp() -- for removing pattern bindings in Pfe3Cmds.
import TiModule() -- instance ValueId PNT
import TiProp()
import RemoveListCompProp()
import SimpPatMatchProp()

import TiPropDecorate(TiDecls) -- to choose result type from the type checker
--import PropSyntax(HsDeclI) -- to choose result type from the type checker
import HsModule

--import Pfe3Cmds(pfe3Cmds)
import Pfe4Cmds(pfe4Cmds)
import PFE4(PFE4Info,runPFE4Cmds)
import PfeHtmlCmds(pfeHtmlCmds)
import PfeChase(pfeChaseCmds)
import ASTCmds

main =
  do (opts,name,args0) <- getPPopts
     --lexerflags1 <- fromMaybe lexerflags0 # readFileMaybe lexerflagsPath
     lexerflags1 <- return lexerflags0 -- grr!
     let (lexerflags,args1) = lexerOptions lexerflags1 args0
     runPFE4Cmds () pfeCmds (pLexerPass0 lexerflags,parse) (opts,name,args1)

pfeCmds = pfe4Cmds tcOutput++
          pfeChaseCmds++
          pfeHtmlCmds++
	  astCmds


-- The type checker can output (TiDecls i2) or [HsDeclI i2].
tcOutput = id :: I (PFE4Info i2 (TiDecls i2))
type I a = a->a
