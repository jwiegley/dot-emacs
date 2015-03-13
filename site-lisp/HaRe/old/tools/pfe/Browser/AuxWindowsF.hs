module AuxWindowsF where
import AllFudgets
import FudExtras(staticHyperGraphicsF')
import ContribFudgets(delayedAuxShellF)
--import ContribFudgets(menuBarF,subMenuItem,toggleItem,Transl(..))


auxGfxWindowsF maintitle = auxWindowsF windows
  where
    windows = [(tag,gfxDispShellF (show tag))|tag<-[minBound..maxBound]]

    gfxDispShellF title = delayedAuxShellF longtitle gfxDispF
      where
        longtitle = maintitle++": "++title
	gfxDispF = scrollF (staticHyperGraphicsF' pm initD)
	pm = setSizing Dynamic
        initD = blankD (pP 440 220)

auxWindowsF auxwindows =
    {-loopThroughRightF-} windowsF {-auxWindowsMenuF-}
  where
    windowsF = post >^=< listF auxwindows -- >=^< pre
      where
        --pre (w,Left b) = (w,Left b)
	--pre (w,Right i) = (w,Right i)

	post (w,Left b) = Left (w,b)
	post (w,Right o) = Right (w,o)
{-
    auxWindowsMenuF =
        nameF "AuxWindowsMenu" $
        menuBarF [subMenuItem idT ws "Windows"]
      where
        ws = [wtoggle tag tag|(tag,window)<-auxwindows]
        wtoggle w = toggleItem (tr w) False
	tr w = Transl ((,) w) (\ (w',b) -> if w'==w then Just b else Nothing)

    idT = Transl id Just -- why not this?
-}
