module PfeBrowserGUI(module PfeBrowserGUI,posLabel) where
import List(groupBy,sortBy)
import Maybe(isNothing)
--import Char(isSpace)

import AllFudgets
import FudExtras(popupMenuF',staticHyperGraphicsF')
import ContribFudgets(menuIcon,item,itemValue)--menuBarF,delayedSubMenuItem,idT,cmdItem
import HyperGraphicsF2
import TreeBrowser as B(treeBrowserF',Tree(..))
import HistoryButtonsF
import ListUtil(chopList,breakAt,mapFst)

import PfePlumbing
import PfeBrowserColors as C
import DrawLex(drawLex,fakeLex,posLabel,rootLabel,isCertAnnot)

import HsLexerPass1(lexerPass0)
import HsTokens as T
import HsName(ModuleName(..),parseModuleName)

import OpTypes(cmpBy)
import PrettyPrint(pp,(<+>))
import MUtils(apSnd)

textEditorPopupF = 
    inputPopupF "Editor" (spF $ oldScrollF True (500,600) inputEditorF) Nothing
  where spF = spacer1F (noStretchS False False)

newCertPopupF :: F ToNewCertPopup FromNewCertPopup
newCertPopupF =
    snd>^=<inputPopupF title newCertF Nothing >=^< pre
  where
    title = "Create a new certificate"
    pre inp = (Just title,Just inp)

newCertF = tableF 2 (typeF `inputPairF` (nameF `inputPairF` conclF))
  where
    typeF = labelF "Type" >*<
              (inputChange>^=<dynF nullLF
               >=^< Left . radioButtonsF>=^^<idempotSP>=^<map certTypeItem)
    radioButtonsF [] = labelF "No certificate types available?!"
    radioButtonsF items@(item1:_) =
      radioGroupF [(itemValue item,item)|item<-items] (itemValue item1)

    nameF = labelF "Name" >*< stringF
    conclF = labelF "Conclusion" >*< stringF

    certTypeItem (cert,(icon,_,_)) = item cert (hboxD [g icon,g cert])

graphDispF :: F ToGraph FromGraph
graphDispF =
    mapFilterSP leaf>^^=<
    vScrollF (treeBrowserF' g0)>=^<graphTree.sortBy (cmpBy (fst.snd))
  where
    g0 = graphTree []
    leaf (B.Leaf l) = Just (itemValue l)
    leaf _ = Nothing

    graphTree g =
	Node "Module Graph" [Node "Files" (filepaths2trees g),
			     Node "Modules" (map mitem g)]
      where
	mitem n@((_,(m,_))) = B.Leaf (item n (pp m))

    filepaths2trees = list2trees . map withpath
      where
	list2trees = map tree . groupBy eqHead . sortBy (cmpBy fst)

	--tree ([]:_) = ??
	tree [([f],p)] = B.Leaf (item p f)
	tree ((x:xs,p):ys) = Node x (list2trees ((xs,p):mapFst tail ys))

	eqHead (x:xs,_) (y:ys,_) = x==y
	eqHead ([],_) ([],_) = True
	eqHead _ _ = False

	withpath n@(path,_) = (chopList (breakAt '/') path,n)

refDispF :: F ToRefs InfoLbl
refDispF = scrollF (staticHyperGraphicsF' pm initD)
  where pm = setSizing Dynamic . setFont refFont
        initD = padD 20 $ g $
		 "Welcome to the "++myversion++"!"

data ModPos = MP ModuleName (Maybe Label) deriving (Eq)

instance Graphic ModPos where
  measureGraphicK (MP m optpos) =
      measureGraphicK (pp $ m<+>fmap (line.lblPos) optpos)

nodeInfoF :: F ToNodeInfo FromNodeInfo
nodeInfoF =
    --simpleGroupF [] $
    vBoxF (fileF>*<hBoxF (historyF>*<nodeF))
  where
      -- Input is: ((f,(n,is)),es)+Pos

    fileF = Right >^=< ldispF  "File:" >=^< fst.fst >=^^< filterLeftSP

    historyF =
        post >^=<
        loopThroughRightF (absF ignore0)
		          (historyButtonsF{- >==< teeF show "history: "-})
        >=^< mpos
      where
	mpos = mapEither mpos1 mpos2
        mpos1 ((f,(n,is)),es) = MP n Nothing
	mpos2 (m,p) = MP m (Just p)
	post (MP m optpos) = Left (m,optpos)

	ignore0 = getSP $ either repeat (either makehistory (const ignore0))

	repeat cur = putSP (Right cur) $ ignore cur
	makehistory new = putSP (Left (Left new)) $ ignore new
	replace new = putSP (Left (Right new)) $ ignore new

	ignore cur@(MP m op) = getSP $ either repeat (either newmod updpos)
          where
	    newmod new@(MP m' Nothing) | m'==m = ignore cur
	    newmod new = makehistory new

	    updpos new | new==cur = ignore cur
	    updpos new@(MP m' _) | m'==m && isNothing op = replace new
	    updpos new = makehistory new

    nodeF = (moduleF>*<dynImportMenusF)  >=^^< filterLeftSP
    moduleF = post . parseModuleName >^=< ldispF "Module:" >=^< pp.fst.snd.fst
      where post m = Left (m,Nothing)

    ldispF l = l `labLeftOfF` strF
      where strF = stringInputF --' (setSizing Dynamic)

    dynImportMenusF =
       dynModuleMenuF "Imports" >=^< snd.snd.fst
        >*<dynModuleMenuF "Imported By" >=^< snd
 
    dynModuleMenuF lbl = popupMenuF' 1 [] (menuLblF lbl)>=^<pre
      where pre ms = Left [((m,Nothing),pp m)|m<-take 30 ms]
			   -- !! no indication if menu is truncated

    menuLblF lbl = labelF' pm (hboxcD [g lbl,g menuIcon])
      where pm = setBorderWidth 1 . setBgColor paperColor

    --fud1>|<fud2 = stripEither>^=<prodF fud1 fud2

sourceDispF :: F ToSource FromSource
sourceDispF =
    wCreateGCtx rootGCtx (gcFontA sourceFont) $ \ gctx ->
    loadColorsF gctx sourceDispF'

sourceDispF' colgc =
    scrollF (mousePointSP>^^=<hyperGraphicsF2' pm init)>=^<either replace id
  where
    pm = setFont sourceFont . setGfxEventMask [GfxButtonMask,GfxMotionMask]
    init = drawLex undefined undefined undefined colgc [] [] [] empty
    empty = lexerPass0 (replicate 24 '\n'++replicate 80 ' ') -- for initial size
    replace (dir,icons,(path,(m,_)),ts,rs,cs,na) =
      replaceGfx rootLabel $ drawLex dir icons m colgc rs cs na ts

    mousePointSP = idempotSP -==- mapFilterSP label
      where
        label event =
          do (lbl,_):_ <- gfxEventPaths event
	     case event of
	       GfxButtonEvent {gfxType=Pressed,gfxButton=b} -> Just (Just b,lbl)
	       GfxMotionEvent {} -> Just (Nothing,lbl)
	       _ -> Nothing

highlightGfxs off on = ChangeGfx $ change off False++change on True
  where change paths on = [(path,(on,Nothing))|path<-paths]

hilite off on = Right (highlightGfxs off on)
mkvis lbl = Right (ShowGfx lbl (Nothing,Nothing))
setwaitcursor =  Right (ChangeGfxFontCursor 150)
setlinkcursor =  Right (ChangeGfxFontCursor 60)
setnormalcursor = Right (ChangeGfxCursor cursorNone)
showsrctext = Right . replaceGfx rootLabel . fakeLex

isCertTokenRef = isCertToken . fst
isCertToken token =
  do (NestedComment,(_,s)) <- return token
     isCertAnnot s


-- Moved file path definitions to ../../property/pfe/PFE_Certs.hs

sourceFont = argKey "sourcefont" defaultFont
refFont = argKey "reffont" defaultFont
