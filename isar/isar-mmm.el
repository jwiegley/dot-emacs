;; isar-mmm.el	  Configure MMM mode for Isar (for LaTeX, SML mode)
;;
;; Copyright     (C) 2003 David Aspinall
;; Authors:       David Aspinall <da@dcs.ed.ac.uk>
;; Licence:	 GPL
;;
;; $Id$
;; 
;; TODO: more insertion commands might be nice.
;; (Presently just C-c % t and C-c % M)
;;

(require 'mmm-auto)

(defconst isar-start-latex-regexp 
  (concat
   "\\(" 
   (proof-ids-to-regexp (list "text" "header" ".*section"))
   "\\)[ \t]+{\\*"))

(defconst isar-start-sml-regexp 
  (concat
   "\\(" 
   (proof-ids-to-regexp (list "ML" "ML_command" "ML_setup"
			      "typed_print_translation"))
   "\\)[ \t]+{\\*"))


(mmm-add-group
 'isar
 `((isar-latex
   :submode LaTeX-mode
   :face mmm-comment-submode-face
   :front ,isar-start-latex-regexp 
   :back  "\\*}"
   :insert ((?t isartext nil @ "text {*" @ " " _ " " @ "*}" @))
   :save-matches 1)

  (isar-sml
   :submode sml-mode
   :face mmm-code-submode-face
   :front ,isar-start-sml-regexp
   :back  "\\*}"
   :insert ((?M isarml nil @ "ML_setup {*" @ " " _ " " @ "*}" @))
   :save-matches 1)))
   

(provide 'isar-mmm)

;;; isar-mmm.el ends here
