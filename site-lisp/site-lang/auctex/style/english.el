;;; english.el --- Setup AUCTeX for editing English text.

;;; Code:

(TeX-add-style-hook
 "english"
 (lambda ()
   (unless (eq (car TeX-quote-language) 'override)
     (setq TeX-quote-language nil))
   (run-hooks 'TeX-language-en-hook))
 LaTeX-dialect)

;;; english.el ends here
