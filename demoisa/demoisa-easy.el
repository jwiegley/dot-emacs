;; demoisa-easy.el Example Proof General instance for Isabelle
;;
;; Copyright (C) 1999 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; This is an alternative version of demoisa.el which uses the
;; proof-easy-config macro to do the work of declaring derived modes,
;; etc.  
;;
;; This mechanism is in fact recommended for new instantiations of
;; Proof General since it follows a regular pattern, and we can more
;; easily adapt the it in the future to new versions of Proof General.
;; It is easy to augment with additional elisp functions and
;; other settings.
;;
;; See demoisa.el and the Proof General manual for more documentation.
;;
;; To test this file you must rename it demoisa.el.
;;

(require 'proof-easy-config)            ; easy configure mechanism

(proof-easy-config 
 'demoisa "Isabelle Demo" 
 proof-prog-name		 "isabelle"
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
 "^\\(val it = () : unit\n\\)?ML>? "
 proof-shell-error-regexp             
 "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
 proof-shell-init-cmd  
 "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 proof-shell-proof-completed-regexp "^No subgoals!"
 proof-shell-eager-annotation-start   
 "^\\[opening \\|^###\\|^Reading")

(provide 'demoisa)