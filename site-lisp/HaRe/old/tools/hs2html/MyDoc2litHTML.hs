module MyDoc2litHTML(litHTML) where

import MyDoc
import Pretty

litHTML = Style
    { ppHeading     = heading
    , ppDecStr      = txt
    , ppCode        = code

    , ppList        = list
    , ppItem        = item

    , ppParagraph   = par
    , ppText        = markHTML
    , ppFinalize    = id
    } 

tag t       = char '<' <> text t <> char '>'
endtag t    = text "</" <> text t <> char '>'

tagL t d    = tag t <> d <> endtag t 

heading (n,t) = tagL ('H' : show (n + 1)) (text t)
txt (x,t) = f (text t)
    where 
    f = case x of
        Plain   -> id
        Emph    -> tagL "I"
        Code    -> tagL "TT"
        Math    -> tagL "I"

list        = tagL "UL" . vcat
code        = vcat . map text
item        = tagL "LI"
par         = tagL "P"

markHTML x  = text "{-+" <+> x <+> text "-}"
