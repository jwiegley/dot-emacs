;;; amsart.el --- Style hook for the AMS-LaTeX article document class.

;;; Code:

(TeX-add-style-hook "amsart"
 (function
  (lambda ()
    (TeX-run-style-hooks "amsmath" "amsthm")
    (LaTeX-add-environments "abstract")))
 LaTeX-dialect)

;;; amsart.el ends here.
