;; isar-mmm.el	  Configure MMM mode for Isar (for LaTeX, SML mode)
;;
;; Copyright     (C) 2003 David Aspinall
;; Authors:       David Aspinall <da@dcs.ed.ac.uk>
;; Licence:	 GPL
;;
;; $Id$
;; 
;; Presently, we deal with several cases of {* text *}.
;; It's not a good idea to do too much, since searching for the
;; regions and fontifying them is slow.
;; 
;; TODO:
;;  --- fontification for antiquotations has been lost, could
;;      add that into LaTeX mode somehow.
;;  --- support for X-Symbols inside MMM mode?  (eek)
;;  --- more insertion commands might be nice.
;;      (Presently just C-c % t and C-c % M)
;;

(require 'mmm-auto)

(defconst isar-start-latex-regexp 
  (concat
   "\\(" 
   (proof-ids-to-regexp 
    ;; Perhaps section is too much?  The fontification is nice but
    ;; section headers are a bit short to use LaTeX mode in.
    (list "text" "header" ".*section"))  
   ;; Next one is nice but hammers font lock a bit too much
   ;; if there are lots of -- {* short comments *}
   ;; "\\|\-\-" ;; NB: doesn't work with \\<--\\>
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
