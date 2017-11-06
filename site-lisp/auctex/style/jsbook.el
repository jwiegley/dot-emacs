;;; jsbook.el - Special code for jsbook class.

;;; Code:

(defvar LaTeX-jsbook-class-options
  '("a3paper" "a4paper" "a5paper" "a6paper" "b4paper" "b5paper" "b6paper"
    "a4j" "a5j" "b4j" "b5j" "a4var" "b5var" "letterpaper" "legalpaper"
    "executivepaper" "landscape" "report"
    "8pt" "9pt" "10pt" "11pt" "12pt" "14pt" "17pt" "20pt" "21pt" "25pt"
    "30pt" "36pt" "43pt" "12Q" "14Q" "usemag" "nomag" "nomag*"
    "tombow" "tombo" "mentuke" "oneside" "twoside" "vartwoside"
    "onecolumn" "twocolumn" "titlepage" "notitlepage"
    "openright" "openleft" "openany" "leqno" "fleqn"
    "disablejfam" "draft" "final" "mingoth" "wingoth" "jis"
    "uplatex" "autodetect-engine" "papersize" "english" "jslogo" "nojslogo")
  "Class options for the jsbook class.")

(TeX-add-style-hook
 "jsbook"
 (lambda ()
   (if (LaTeX-provided-class-options-member "jsbook" "report")
       (progn
	 (LaTeX-largest-level-set "chapter")
	 (LaTeX-add-environments "abstract"))
     (LaTeX-largest-level-set "part"))
   (LaTeX-add-counters "part" "chapter" "section" "subsection" "subsubsection"
		       "paragraph" "subparagraph" "figure" "table")
   (LaTeX-add-pagestyles "headings" "myheadings"))
 LaTeX-dialect)

;;; jsbook.el ends here
