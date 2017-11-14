;;; jarticle.el - Special code for jarticle class.

;;; Code:

(defvar LaTeX-jarticle-class-options
  '("a4paper" "a5paper" "b4paper" "b5paper" "a4j" "a5j" "b4j" "b5j"
    "a4p" "b4p" "b5p" "10pt" "11pt" "12pt" "landscape" "tombow" "tombo"
    "mentuke" "oneside" "twoside" "onecolumn" "twocolumn"
    "titlepage" "notitlepage" "leqno" "fleqn"
    "openbib" "disablejfam" "mathrmmc" "draft" "final")
  "Class options for the jarticle class.")

(TeX-add-style-hook
 "jarticle"
 (lambda ()
   (LaTeX-largest-level-set "section")
   (LaTeX-add-counters "part" "section" "subsection" "subsubsection" "paragraph"
		       "subparagraph" "figure" "table")
   (LaTeX-add-pagestyles "headings" "myheadings")
   (LaTeX-add-environments "abstract"))
 LaTeX-dialect)

;;; jarticle.el ends here
