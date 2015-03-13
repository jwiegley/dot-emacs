module Attrs where
import List(isPrefixOf)

{-+
Types for attributes. Both certificate servers and certificates have attributes.
-}
type Name = String -- Tag
type Value = String
type Attr = (Name,Value)
type Attrs = [Attr]

printAttrs :: Attrs->String
printAttrs = unlines . map printAttr

printAttr :: Attr->String
printAttr (name,value) = name++": "++value

{-+
Certificate attributes called file or file/xxx are assumed to refer to files
that are required to validate a certificate. 
-}
namesFile :: Name -> Bool
namesFile name = takeWhile (/='/') name=="file"

