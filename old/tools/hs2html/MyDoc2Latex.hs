module MyDoc2Latex(latex) where

import MyDoc
import Pretty


beg t = text "\\begin{" <> text t <> char '}'
end t = text "\\end{" <> text t <> char '}'

cmd x t = beg x $$ t $$ end x


latex = Style
    { ppHeading     = heading
    , ppDecStr      = txt
    , ppCode        = code

    , ppList    = list
    , ppItem    = item

    , ppParagraph   = par
    , ppText        = id
    , ppFinalize    = fin
    }


fin x = text "\\documentclass{article}"
      $$ cmd "document" x

heading (n,t) = text lvl <> curlies (text t)
    where
    lvl = case n of    
        0 -> "\\section" 
        1 -> "\\subsection"
        2 -> "\\subsubsection"
        _ -> error "*** section level > 3"

txt (dec,t) = let t' = text t in case dec of
    Plain   -> t'
    Emph    -> text "\\emph" <> curlies t'
    Code    -> text "\\verb#" <> t' <> char '#' 
    Math    -> char '$' <> t' <> char '$'

list    = cmd "itemize" . vcat 
item i  = text "\\item" <+> i
par t   = text "\n" $$ t

code = cmd "verbatim" . vcat . map text 


