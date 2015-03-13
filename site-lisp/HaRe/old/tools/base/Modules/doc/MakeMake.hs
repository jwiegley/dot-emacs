import Pretty

src_dir = text ".."
names   = map text ["Modules","NamesEntities","CheckModules","Relations",
		    "ModSysAST","ModSysSem"]

description     = text "Description"
formats         = [".dvi", ".pdf", ".ps"]
main_targets    = (hsep $ map (description <>) $ map text formats) 
tex_files       = hsep $ map toTex (names ++ map text 
                [ "related_work", "abstract", "conclusion", "intro"])

src_deps        = tex_files <+> text "Description.bbl" <+> text "pphs.sty"


makefile = text "all:" <+> main_targets 

        $$ text "Description.dvi:" <+> src_deps
        $$ latex <+> description

        $$ text "Description.pdf:" <+> src_deps
        $$ pdflatex <+> description

        $$ text "Description.ps:  Description.dvi"
        $$ dvips <+> text "Description.dvi -o Description.ps"

        $$ text "Description.bbl: Description.tex Description.bib"
        $$ latex <+> description
        $$ bibtex <+> description

        $$ vcat (map target names)

        $$ text "tmp:" 
        $$ mkdir <+> text "tmp"

        $$ text "clean:"
        $$ rm <+> main_targets 
        $$ rm <+> text "tmp/*"
        $$ rm <+> text "*.log *.aux *.blg"


toTex n = n <> text ".tex"
toSrc n = src_dir <> char '/' <> n <> text ".lhs"

target n = tex <> char ':' <+> src <+> text "tmp"
        $$ hack <+> src <+> to <+> tex
    where
    src = toSrc n
    tex = toTex n

-- commands

tab         = char '\t'
to          = char '>'
hack        = tab <> text "./Hack"
rm          = tab <> text "-rm"
mkdir       = tab <> text "mkdir"
latex       = tab <> text "latex"
pdflatex    = tab <> text "pdflatex"
dvips       = tab <> text "dvips -t letter"
bibtex      = tab <> text "bibtex"

main = putStrLn $ render makefile


