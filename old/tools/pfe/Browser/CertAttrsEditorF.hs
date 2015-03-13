module CertAttrsEditorF where
import Maybe(fromMaybe)
import Fudgets
import Attrs
import CertAttrs
import CertServers(serverName,certAttrs)

dynCertAttrsEditorPopupsF =
    dynF nullF >=^< mapEither certAttrsEditorPopupsF id

certAttrsEditorPopupsF = listF . map edF
  where
    edF s = (n,attrsEditorPopupF n (certAttrs s))
      where n = serverName s

attrsEditorPopupF ctype attrs =
    post >^=< inputPopupF title (attrsEditorF attrs) Nothing >=^< pre
  where
    title = ctype++" certificate Attribute Editor"

    pre (cname,cattrs) = (Just cname,Just cattrs)
    post ((Just cname,_),attrs) = (cname,attrs)

attrsEditorF :: CertAttrs -> InF Attrs Attrs
attrsEditorF attrs =
    placerF (tableP 2) $
    inputListF [(name,attrEditorF attr)|(name,attr)<-attrs] >=^< pre
  where
    pre cattrs = map (pickattr cattrs) attrs

    pickattr cattrs (aname,attr) =
      (aname,fromMaybe (fromMaybe "" (adefault attr)) (lookup aname cattrs))


attrEditorF Attr {atype=t,label=lbl} = labelF lbl >*< attrEditorF' t

attrEditorF' t =
  case t of    
    String -> stringF
    File -> stringF -- !!
    Nat -> stringF -- !!!
    Bool -> inputChange.show>^=<spacer1F leftS (toggleButtonF "")>=^<(=="True")
