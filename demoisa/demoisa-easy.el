;; demoisa-easy.el Example Proof General instance for Isabelle
;;
;; Copyright (C) 1999 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; This is an alternative version of demoisa.el which uses the
;; proof-easy-config mechanism to avoid declaring derived modes, etc.
;;
;; NB: proof-easy-config is experimental, and only works with XEmacs.
;;
;; See demoisa.el for documentation.
;;
;; To test this file you must rename it demoisa.el.
;;
;; It relies on this line in proof-assistant-table:
;;  demoisa "Isabelle Demo" "\\.ML$"
;;

(require 'proof-easy-config)            ; easy configure mechanism

(proof-easy-config 
 'demoisa "Isabelle Demo" 
 demoisa-prog-name		   "isabelle"
 demoisa-terminal-char             ?\;
 demoisa-comment-start             "(*"
 demoisa-comment-end               "*)"
 demoisa-goal-command-regexp       "^Goal"
 demoisa-save-command-regexp       "^qed"
 demoisa-goal-with-hole-regexp     "^Goal \\(\\(\"%s\"\\)\\)"
 demoisa-save-with-hole-regexp     "^qed \\(\\(\"%s\"\\)\\)"
 demoisa-non-undoables-regexp      "undo\\|back"
 demoisa-undo-n-times-cmd          "pg_repeat undo %s;"
 demoisa-showproof-command       "pr()"
 demoisa-goal-command              "Goal \"%s\";"
 demoisa-save-command              "qed \"%s\";"
 demoisa-kill-goal-command         "Goal \"PROP no_goal_set\";"
 demoisa-auto-multiple-files       t
 demoisa-shell-cd-cmd              "cd \"%s\""
 demoisa-shell-prompt-pattern      "[ML-=#>]+>? "
 demoisa-shell-interrupt-regexp    "Interrupt"
 demoisa-shell-start-goals-regexp  "Level [0-9]"
 demoisa-shell-end-goals-regexp    "val it"
 demoisa-shell-quit-cmd            "quit();"
 demoisa-assistant-home-page    
 "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
 demoisa-shell-annotated-prompt-regexp 
 "^\\(val it = () : unit\n\\)?ML>? "
 demoisa-shell-error-regexp             
 "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
 demoisa-shell-init-cmd  
 "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 demoisa-shell-demoisa-completed-regexp   
 "\\(\\(.\\|\n\\)*No subgoals!\n\\)"
 demoisa-shell-eager-annotation-start   
 "^\\[opening \\|^###\\|^Reading")
