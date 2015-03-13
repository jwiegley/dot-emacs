module MyDoc2HTML(html,htmlblock) where

import MyDoc
import Text.PrettyPrint hiding (Style)

htmlblock = html { ppFinalize = id }

html = Style
    { ppHeading     = heading
    , ppDecStr      = txt
    , ppCode        = code

    , ppList        = list
    , ppItem        = item

    , ppParagraph   = par
    , ppText        = id
    , ppFinalize    = fin
    } 

tag t       = char '<' <> text t <> char '>'
endtag t    = text "</" <> text t <> char '>'

tagB t d    = tag t $$ d $$ endtag t 
tagL t d    = tag t <> d <> endtag t 

heading (n,t) = tagL ('H' : show (n + 1)) (text t)
txt (x,t) = f (text t)
    where 
    f = case x of
        Plain   -> id
        Emph    -> tagL "I"
        Code    -> tagL "TT"
        Math    -> tagL "I"

list        = tagB "UL" . vcat
code        = tagB "PRE" . vcat . map text
item        = tagL "LI"
par         = tagB "P"

fin         = tagB "HTML" . tagB "BODY"

