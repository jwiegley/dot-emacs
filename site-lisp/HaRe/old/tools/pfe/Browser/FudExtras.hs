module FudExtras where
import AllFudgets


--longTextPopupF = longTextPopupF' okButtonF
longTextPopupF = stripEither >^=< popupsF >=^< route
  where
    popupsF = messagePopupF >+< longTextPopupF' okButtonF

    route msg = (if length msg <= 1 then Left else Right) msg

longTextConfirmPopupF = longTextPopupF' buttonsF
  where
    buttonsF = post>^=<hBoxF (okButtonF>+<cancelButtonF)
    post = either (const Confirm) (const Cancel)

longTextChoicePopupF =
    post >^=< longTextPopupF'' buttonsF (concatMapSP pre)
  where
    post ((txt,(lbl1,lbl2)),choice) = either (const lbl1) (const lbl2) choice

    pre (txt,(lbl1,lbl2)) = [Right (Left lbl1),Right (Right lbl2),Left txt]

    buttonsF = hBoxF (dynButtonF "Yes" >+< dynButtonF "No")
    dynButtonF lbl = buttonF'' standard lbl >=^< Left . setLabel

---
longTextPopupF' buttonsF = longTextPopupF'' buttonsF (mapSP Left)

longTextPopupF'' buttonsF pre =
  popupShellF "Confirm" Nothing
    (filterRightSP>^^=< vBoxF (moreF>+<buttonsF)>=^^<pre)

okButtonF = spacer1F leftS $ kbuttonF "Return" "OK"
cancelButtonF = spacer1F rightS $ kbuttonF "Escape" "Cancel"

kbuttonF k = buttonF' (setKeys [([],k)])

---

-- Like popupMenuF, but allow you to specify which button should pop up the menu
popupMenuF' button alts f =
    mapEither fstEqSnd id>^=<
    oldPopupMenuF bgColor True menuFont (Button button) [] []
                  (pre alts) sndEqSnd f
    >=^< mapEither pre id
  where
    pre = map (`pair` []) . toEqSnd


newtype NoEq a = NoEq a 
instance Eq (NoEq a) where _==_ = True

staticHyperGraphicsF' pm initD =
    post >^=< hyperGraphicsF' pm initD>=^<Left . pre
  where
    pre = mapLabelDrawing NoEq
    post (NoEq lbl) = lbl
