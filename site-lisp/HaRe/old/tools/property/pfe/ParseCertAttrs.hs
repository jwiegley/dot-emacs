module ParseCertAttrs(parseCertAttr,CertAttrs) where
import CertAttrs
import OneLineAttrs
import Monad(mplus)
import MUtils

parseCertAttr :: String -> Maybe (Name,CertAttr)
parseCertAttr s = certAttrs =<< parseOneLineAttrs s

certAttrs attrs = (,) # attr "name" <# certAttrsFields
  where
    certAttrsFields = Attr # atype <# label <# return adefault

    atype = atypeP =<< attr "type"
    label = attr "label" `mplus` attr "name"
    adefault = attr "default"

    atypeP s =
      case break (=='/') s of
	("string","/file") -> return File
	("string",_) -> return String
	("nat","") -> return Nat
	("bool","") -> return Bool
	_ -> fail $ "Unknown attribute type: "++s
	     -- Error message is lost when using the Maybe monad.

    attr a = lookup a attrs
