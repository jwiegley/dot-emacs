;;; thin-quantifiers.el --- Make spaces after quantifiers thinner

;;; Commentary:

;;; Code:

(defconst space-after-quantifier-width 0.666)

(font-lock-add-keywords nil '(("\\(?:forall\\|exists\\|∀\\|∃\\)\\( \\)" 1
                       `(face nil display (space :relative-width ,space-after-quantifier-width)))))

(provide 'thin-quantifiers)
;;; thin-quantifiers.el ends here
