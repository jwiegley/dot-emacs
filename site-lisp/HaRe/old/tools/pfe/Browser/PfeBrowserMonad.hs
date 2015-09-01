module PfeBrowserMonad where
import Maybe(isJust)
import Monad(when)
import MT(lift)
import AbstractIO

import FudgetIOMonad1
import PfePlumbing
import PfeBrowserMenu(WindowCmd,ViewCmd,MenuCmd(..),WindowCmd(..))
import PfeBrowserGUI
import PNT(PNT)
import SimpleGraphs(Graph)

import PropParser(parse)
import PropLexer({-LexerFlags,-}pLexerPass0)
import PPU(PPHsMode)
import TiPropDecorate(TiDecls) -- to choose result type from the type checker
import PropPosSyntax(Id,HsName,HsDecl)
import FreeNamesProp()
import ScopeNamesProp()
import NameMapsProp()
import ReAssocProp()
import MapDeclMProp() -- for removing pattern bindings in Pfe3Cmds.
--import TiModule() -- instance ValueId PNT
import TiProp()
import PFE4
import PFEdeps
import PFE0
import PFE_Certs
import CertCmd(CertCmd)

type Opts = ({-LexerFlags,-}((Bool, PPHsMode), String, [String]))

-- PFE Browser monad:
--type PfeFM = PFE0MT Id HsName [HsDecl] () (WithState PfeBrowserState FIOM)
--type PfeFM = WithState PfeBrowserState (PFE0MT Id HsName [HsDecl] () FIOM)
type PfeFM = PFE5MT Id HsName PNT [HsDecl] (TiDecls PNT) PfeBrowserState FIOM


runPfeFM pfeFM ({-lexeropts,-}opts) =
    runPFE5 undefined (\n a->pfeFM) (pLexerPass0 {-lexeropts-},parse) opts

pfeGet = lift getFM :: PfeFM In
pfePut = lift . putFM
pfeQuit = lift quitFM

withWaitCursor :: PfeFM a -> PfeFM a -- polymorphic recursion...
withWaitCursor cmd =
  do pfePut (toSource setwaitcursor)
     tryThen cmd $ pfePut (toSource setnormalcursor)

putInfoWindow (w,x) = pfePut . toInfoWindows $ (w,Right x)

popupInfoWindow (w,up) =
  do pfePut (toMenuBar (Windows (WindowCmd w up)))
     when (not up && w==CertInfo) $
       updStBr $ \ st ->st{certDisplay=Nothing}

popupCertInfo qcert info =
    do putInfoWindow (CertInfo,info)
       popupInfoWindow (CertInfo,True)
       updStBr $ \ st -> st{certDisplay=Just qcert}

getStBr :: PfeFM PfeBrowserState
updStBr :: (PfeBrowserState->PfeBrowserState)->PfeFM ()

getStBr = getSt5ext
updStBr = updSt5ext
setStBr = updStBr . const

type TInfo = PFE4Info PNT (TiDecls PNT)
type ViewMode = ViewCmd

data PfeBrowserState
   = St { -- Mode
	  viewMode :: ViewMode,
          -- The selected module:
	  modnode::ModuleNode,
	  mrefs::[XRefInfo],hilbls::[Label],
	  types::Maybe TInfo,
	  certs::[CertInfo],
	  -- Project info:
	  revgraph::Graph ModuleName,
	  -- Cert display/state info:
	  certDisplay    :: Maybe QCertName,  -- currently displayed cert
	  certInProgress :: [CertCmd],  -- server command in progress or queued
	  -- Project independent info:
	  certServers :: CertServers,
	  certIcons :: CertIcons,
	  sadIcon :: PixmapImage }

haveTypes = isJust . types
modname = fst . snd . modnode
noModuleNode = ("",(undefined,[])) -- for the initial state
isNoModule (path,_) = null path
--sccs = fst . snd . pfe2info
--graph = concat . sccs
icons st = (sadIcon st,certIcons st)
