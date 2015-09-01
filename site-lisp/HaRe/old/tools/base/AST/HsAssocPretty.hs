module HsAssocPretty where
import HsAssocStruct
import PrettyPrint

instance Printable HsFixity where
    ppi (HsFixity assoc n) = assoc <+> lit n

instance Printable HsAssoc where
    ppi HsAssocNone  = kw "infix"
    ppi HsAssocLeft  = kw "infixl"
    ppi HsAssocRight = kw "infixr"

