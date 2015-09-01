module PfePlumbing(module PfePlumbing,module P) where
import AllFudgets as P(PixmapImage,Drawing,Gfx,Graphic(..),Button,Click,GfxCommand)

import PFE0 as P(ModuleNode,ModuleGraph)
import PFE_Certs as P(CertType,CertName,QCertName,CertStatus)
import HsModule as P(ModuleName)
import HsTokens as P(Token)
import HsLexerPos as P(Pos(..))
--import RefsTypes(Orig,Refs,isDef)
import ScopeModule as P(XRefInfo)
import PNT(PNT)
import HsIdent(HsIdentI)
import SrcLoc(SrcLoc,srcPath,srcLoc)
import ConvRefsTypes(simpSrcLoc)
import NameMaps(Role(..),Context(..))
import TypedIds(IdTy(Assertion))
import PfeBrowserMenu as P(MenuCmd)
import OpTypes(eqBy,cmpBy)
import CertServers as P(CertServers,Attrs,Name)
import CertCmd(CertCmd)
import StatusIndicator(Status)
import Now(compileDate)

myname = "Programatica Haskell Browser"
myversion = myname++" version "++compileDate

type Refs=[XRefInfo]
type Orig=XRefInfo

type CertIcons = [(CertType,(PixmapImage,PixmapImage,PixmapImage))]
                           --(valid,invalid,unknown)
type Icons = (PixmapImage,CertIcons) -- (bad,certicons)
type CertsStatus = [(CertName,CertStatus)]
type CertsNoAnnot = [(String{-AssertionName-},[CertName])]

type SrcToken = (Token,(Pos,String))
newtype Label = Lbl {unLbl::(SrcToken,Maybe Orig)} --deriving (Show)

lblPos = fst.snd.fst.unLbl

assertionDefLbl (Lbl ((_,(_,s)),Just ((Def _,_),_,[(_,Assertion)]))) = Just s
assertionDefLbl _ = Nothing

isDefLbl (Lbl (_,Just ((r,_),_,_))) = isDef r
isDefLbl _ = False

isDef (Def (Instance _)) = False
isDef (Def _) = True
isDef _ = False

refPos :: XRefInfo -> Pos
addRefPos :: XRefInfo -> (Pos,XRefInfo)
refPos r@(_,n,_) = simpSrcLoc (srcLoc n)
addRefPos r = (refPos r,r)
srcLocLbl loc = SrcLocLbl (srcPath loc,simpSrcLoc loc)

instance Eq Label where (==) = eqBy lblPos
instance Ord Label where compare = cmpBy lblPos

type LexDrawing = Drawing Label Gfx

data InfoWindow
  = CertInfo | CertTypes | PendingCmds
  | ErrorMsg | Evidence | Exports | Interface | Pretty
  deriving (Eq,Show,Bounded,Enum)

data InfoLbl
   = CertLbl CertName
   | DefLbl (HsIdentI PNT) | SrcLocLbl (FilePath,Pos) | ModuleLbl ModuleName
   | CertCmd CertCmd | CreateCert (CertName,String)
   | CertEdit (CertType,(CertName,Attrs))
   | CertShowText String
   | ShowErrorMsg InfoDrawing
   deriving (Show)

type InfoDrawing = Drawing InfoLbl Gfx

instance Graphic InfoWindow where measureGraphicK = measureGraphicK . show

type PfeMenuCmd = MenuCmd InfoWindow

type FromMenuBar = PfeMenuCmd
type FromInfoWindows = Either (InfoWindow,Bool) (InfoWindow,InfoLbl)
type FromGraph = ModuleNode
type FromNodeInfo = Either (ModuleName,Maybe Label) FilePath
type FromSource = (Maybe Button,Label)
type FromRefs = InfoLbl
type FromMessagePopup = Click
type FromModuleDisp = Either FromNodeInfo (Either FromSource FromRefs)

type ToModuleDisp = Either ToNodeInfo (Either ToSource ToRefs)
toSource = _toModuleDisp . Right . Left
toRefs = _toModuleDisp . Right . Right

type FromPopups = Either (Either FromMessagePopup FromNewCertPopup)
		         (Either FromCertAttrsEditors FromTextEditor)
type ToPopups = Either (Either ToMessagePopup ToNewCertPopup)
	               (Either ToCertAttrsEditors ToTextEditor)

type FromCertServer = (Bool,[Either String String])
type ToCertServer = String

type ToNewCertPopup = (CertIcons,(CertName,String))
type FromNewCertPopup = (CertType,(CertName,String))

type ToCertAttrsEditors = Either CertServers (CertType,(CertName,Attrs))
type FromCertAttrsEditors = (CertType,(CertName,Attrs))

type ToTextEditor = (Maybe String, Maybe String)
type FromTextEditor = (ToTextEditor,String)

type ToMenuBar = PfeMenuCmd
type ToInfoWindows = (InfoWindow,Either Bool InfoDrawing)
type ToGraph = ModuleGraph
type ToNodeInfo = Either (ModuleNode,[ModuleName]) -- (...,imported by)
                         (ModuleName,Label) -- add position to history
type ToSource =
    Either (FilePath,Icons,ModuleNode,[SrcToken],Refs,CertsStatus,CertsNoAnnot)
           (GfxCommand Label LexDrawing)
type ToRefs = InfoDrawing
type ToMessagePopup = [String]

data Level = Syntax | Scoping | Typing deriving (Eq,Show,Bounded,Enum)

type ToStatus = (Level,Status)
type FromStatus = ()

type In  = Either (Either (Either (Either FromMenuBar FromStatus)
                                  FromInfoWindows)
			  (Either FromGraph FromModuleDisp))
		  (Either FromPopups FromCertServer)
type Out = Either (Either (Either (Either ToMenuBar ToStatus) ToInfoWindows)
                          (Either ToGraph ToModuleDisp))
	          (Either ToPopups ToCertServer)
toMenuBar = toOut . Left . Left . Left . Left
toInfoWindows = toOut . Left  . Left . Right
_toModuleDisp = toOut . Left . Right . Right
toOut = Right -- see FudgetIOMonad1
