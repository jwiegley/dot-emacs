;; ccc.el - Proof General for the Casl Consistency Checker
;; 
;; Author: Christoph Lüth <cxl@informatik.uni-bremen.de>
;;        
;; This is a fairly straightforward instantiation of Proof General for
;; the Casl Consistency Checker, CCC. 
;;
;; CASL is the standard algebraic specification language, and CCC is a
;; tool to check consistency of CASL specifications.
;; 
;; For more information, hasten thee browser yonder:
;;   http://www.informatik.uni-bremen.de/cofi/ccc

(require 'proof-easy-config)            ; nice and easy does it

(proof-easy-config  'ccc "CASL Consistency Checker" 
 proof-prog-name		 "ccc" ;; must be in your path.
 proof-terminal-char             ?\;
 proof-script-comment-start      "(*"
 proof-script-comment-end        "*)"
 proof-goal-command-regexp       "ccc \".*\";"
 proof-save-command-regexp       "^qeccc"
 proof-goal-with-hole-regexp     "ccc \"\\(\\(.*\\)\\)\"" 
 proof-save-with-hole-regexp     "qeccc \"\\(\\(.*\\)\\)\""
 proof-non-undoables-regexp      nil ;; "undo\\|back"
 proof-goal-command              "ccc \"%s\";"
 proof-save-command              "qeccc \"%s\";"
 proof-kill-goal-command         "abort ();"
 proof-showproof-command         "prt()"
 proof-undo-n-times-cmd          "undo_steps %s;"
 proof-auto-multiple-files       nil 
 proof-shell-cd-cmd              "cd \"%s\""
 proof-shell-prompt-pattern      "^\\(CCC\\|^HOL-CASL\\) > "
 proof-shell-interrupt-regexp    "Interrupt"
 proof-shell-start-goals-regexp  "^No subgoals\\|^[0-9]* subgoals\\|^Wts:"
 proof-shell-end-goals-regexp    "val it"
 proof-shell-quit-cmd            "quit();"
 proof-assistant-home-page       "http://www.informatik.uni-bremen.de/cofi/tools/ccc"
 proof-shell-annotated-prompt-regexp  "^\\(val it = () : unit\n\\)?\\(CCC\\|^HOL-CASL\\)> " ;; "^\\(val it = () : unit\n\\)?ML>? "
 proof-shell-error-regexp        "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
 proof-shell-init-cmd            ""
 proof-shell-proof-completed-regexp "^Consistency proof successfully finished."
 proof-shell-eager-annotation-start "^\\[opening \\|^###\\|^Reading" ;;; ???
 proof-count-undos-fn		'ccc-count-undos
)


;; da: example of a possible count undos function -- replace upper case
;; strings by real stuff

(defun ccc-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let
      ((count-ccc 0) 
       (count-casl 0)
       casl)
    (while span
      (setq str (span-property span 'cmd))
      (if (proof-string-match "HOL-CASL GOAL COMMAND REGEXP" str)
	  (setq casl t))
      (cond ((eq (span-property span 'type) 'vanilla)
             (unless (proof-string-match proof-non-undoables-regexp str)
	       (if casl
		   (setq count-casl (+ 1 count-casl))
		 (setq count-ccc (+ 1 count-ccc))))))
      (setq span (next-span span 'type)))
    (format
     "HOL-CASL UNDOS (%s); CCC-UNDOS (%s);" 
     count-cassl count-ccc)))


(provide 'ccc)


