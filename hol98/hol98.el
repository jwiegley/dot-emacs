;; hol98.el   Basic Proof General instance for HOL 98
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Needs improvement!
;;
;; See the README file in this directory for information.


;; keywords:
;; val prove store_thm prove by
;; tacticals: THEN THENL 
;; by seems to be "e";


(require 'proof-easy-config)            ; easy configure mechanism
(require 'proof-syntax)

(proof-easy-config  'hol98 "HOL" 
 proof-prog-name		 "hol.unquote"
 proof-terminal-char             ?\;
 proof-comment-start             "(*"
 proof-comment-end               "*)"
 proof-goal-command-regexp       "^g[ `]"
 proof-save-command-regexp       "^qed"
 proof-goal-with-hole-regexp     "qed_goal \"\\(\\(.*\\)\\)\""
 proof-save-with-hole-regexp     "qed \"\\(\\(.*\\)\\)\""
 proof-non-undoables-regexp      "b()"
 proof-goal-command              "g `%s`;"
 proof-save-command              "val %s = top_thm(); drop();"
 proof-kill-goal-command         "drop();"
 proof-showproof-command         "p()"
 proof-undo-n-times-cmd          "(pg_repeat backup %s; p());"
 proof-auto-multiple-files       t
; proof-shell-cd-cmd              "cd \"%s\""
 proof-shell-prompt-pattern      "^[->] "
 proof-shell-interrupt-regexp    "Interrupted"
; proof-shell-start-goals-regexp  "Proof manager status\\|OK.."
 proof-shell-start-goals-regexp  
 (proof-regexp-alt "Proof manager status" "OK.." "val it =\n")
 proof-shell-end-goals-regexp    
 (proof-regexp-alt "^[ \t]*: GoalstackPure.goalstack"
		   "^[ \t]*: GoalstackPure.proofs")
 proof-shell-quit-cmd            "quit();"
 proof-assistant-home-page    
 "http://www.cl.cam.ac.uk/Research/HVG/HOL/HOL.html"
 proof-shell-annotated-prompt-regexp 
 "^\\(> val it = () : unit\n\\)?- "
 proof-shell-error-regexp        "^! "
 proof-shell-init-cmd		  
 "Help.displayLines:=3000;
  fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 ;; FIXME: add optional help topic parameter to help command. 
 ;; Have patch ready for PG 3.2, but PG 3.1 is strictly bug fix.
 proof-info-command "help \"hol\""
 proof-shell-proof-completed-regexp   
 "\\(\\(.\\|\n\\)*No subgoals!\n\\)"
; proof-shell-eager-annotation-start
 proof-find-theorems-command	"DB.match [] (%s);"
 ;; We must set this to use ptys since mosml doesn't flush its output
 ;; (on Linux, presumably on Solaris to).
 proof-shell-process-connection-type t
 )

(provide 'demoisa)