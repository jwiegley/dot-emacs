module CertAttrs(module CertAttrs,Name,Value) where
import Attrs(Name,Value)

{-+
Some of the attributes of a certificate server describe what user editable
attributes certificates created by that server contain. The type CertAttrs
is used to represent descriptions of these certificate attributes.
-}

type CertAttrs = [(Name,CertAttr)]

data AType = String | File | Nat | Bool deriving Show

data CertAttr = Attr { atype :: AType,
		       label :: String,
		        --required::Bool, 
		        adefault::Maybe Value }
		deriving Show
