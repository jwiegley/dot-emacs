;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;;                      PARAMÉTRAGE du MODE outline
;;--------------------------------------------------------------------------;;


(setq af2-outline-title-regexp "\\((\\*[ \t\n]*title =\\)")
(setq af2-outline-section-regexp "\\((\\*\\*+\\)")
(setq af2-outline-save-regexp "\\((\\*#\\)")
(setq 
 af2-outline-theo-regexp 
 "\\((\\*lem\\)\\|\\((\\*prop\\)\\|\\((\\*fact\\)\\|\\((\\*theo\\)\\|\\((\\*def\\)\\|\\((\\*cst\\)")
(setq 
 af2-outline-theo2-regexp 
 "\\(lem\\)\\|\\(prop\\)\\|\\(fact\\)\\|\\(theo\\)\\|\\(def\\)\\|\\(cst\\)\\|\\(claim\\)\\|\\(new_\\)")

(setq 
  af2-outline-regexp 
  (concat 
   af2-outline-title-regexp "\\|" 
   af2-outline-section-regexp "\\|" 
   af2-outline-save-regexp "\\|" 
   af2-outline-theo-regexp "\\|" 
   af2-outline-theo2-regexp))

(setq af2-outline-heading-end-regexp "\\(\\*)[ \t]*\n\\)\\|\\(\\.[ \t]*\n\\)")

;(if af2-outline
;    (add-hook 'af2-mode-hook '(lambda()(outline-minor-mode 1)))
;  )

(defun af2-outline-level()
  "Find the level of current outline heading in some af2 libraries."
  (let ((retour 0))
    (save-excursion
      (cond ((looking-at af2-outline-title-regexp) 1)
	    ((looking-at af2-outline-section-regexp)
	     (min 6 (- (match-end 0) (match-beginning 0)))) ; valeur maxi 6
	    ((looking-at af2-outline-theo-regexp) 7)
	    ((looking-at  (concat af2-outline-save-regexp "\\|"
				 af2-outline-theo2-regexp )
			 ) 8)
	    )
      )))

(defun af2-setup-outline ()
  "Set up local variable for outline mode"
  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp af2-outline-heading-end-regexp)
  (make-local-variable 'outline-regexp)
  (setq outline-regexp af2-outline-regexp)
  (make-local-variable 'outline-level)
  (setq outline-level 'af2-outline-level)
  (outline-minor-mode 1)
)

(provide 'af2-outline)