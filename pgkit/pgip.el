;; pgip.el Proof General instance for PGIP protocol (for Isabelle)
;; Copyright (C) 2001 LFCS Edinburgh.
;;
;; Author:              David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Status: experimental, in-progress.

(require 'pg-xml)
(require 'proof-easy-config)

(proof-easy-config 
 'pgip "PGIP Test"
 proof-prog-name                 "~/pgfilt.pl"

 proof-terminal-char             ?\;
 proof-comment-start             "(*"
 proof-comment-end               "*)"
 proof-goal-command-regexp       "^Goal"
 proof-save-command-regexp       "^qed"
 proof-goal-with-hole-regexp     "qed_goal \"\\(\\(.*\\)\\)\""
 proof-save-with-hole-regexp     "qed \"\\(\\(.*\\)\\)\""
 proof-non-undoables-regexp      "undo\\|back"
 proof-goal-command              "Goal \"%s\";"
 proof-save-command              "qed \"%s\";"
 proof-kill-goal-command         "Goal \"PROP no_goal_set\";"
 proof-showproof-command         "pr()"
 proof-undo-n-times-cmd          "pg_repeat undo %s;"
 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "cd \"%s\""
 proof-shell-prompt-pattern      "[ML-=#>]+>? "
 proof-shell-interrupt-regexp    "Interrupt"
 proof-shell-start-goals-regexp  "Level [0-9]"
 proof-shell-end-goals-regexp    "val it"
 proof-shell-quit-cmd            "quit();"



 proof-assistant-home-page    
 "http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"
proof-shell-annotated-prompt-regexp 
 "^\\(val it = () : unit\n\\)?ML>?"

 proof-shell-error-regexp                     
 "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
 ;;proof-shell-init-cmd            (progn
 ;;				   (pg-xml-begin-write)
 ;;			   (pg-xml-openelt 'askpgml)
 ;;		   (pg-xml-closeelt)
 ;;	   (pg-xml-doc))     
 ;; "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));\n"
 proof-shell-proof-completed-regexp "^No subgoals!"
 proof-shell-eager-annotation-start   
 "^\\[opening \\|^###\\|^Reading"

)

(defun pgip-add-markup () 
  (setq string 
	(progn
	  (pg-xml-begin-write)
	  (pg-xml-openelt 'pgip '((version . "\"0.1\"")
				  (class . "\"pa\"")))
	  (pg-xml-writetext string)
	  (pg-xml-closeelt)
	  (pg-xml-doc))))

(add-hook 'proof-shell-insert-hook 
	  'pgip-add-markup)

(provide 'pgip)		



