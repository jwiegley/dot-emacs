;;; graphics.el --- Handle graphical commands in LaTeX 2e.

;;; Code:

(TeX-add-style-hook "graphics"
 (function
  (lambda ()
    (TeX-run-style-hooks "graphicx")
    (setq LaTeX-graphics-package-options LaTeX-graphicx-package-options)))
 LaTeX-dialect)

;;; graphics.el ends here.
