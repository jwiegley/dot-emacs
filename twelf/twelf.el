;; twelf.el  Proof General instance for Twelf
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;;

(require 'proof-easy-config)            ; easy configure mechanism

(require 'twelf-font)			; font lock configuration
;; (require 'twelf-old)			; port of parts of old code

(proof-easy-config 
 'twelf "Twelf" 
 proof-prog-name		 "twelf-server"
 proof-assistant-home-page       "http://www.cs.cmu.edu/~twelf/"
 proof-terminal-char             ?\.
 ;; FIXME: must also cope with single line comments beginning with %
 proof-comment-start             "%{"
 proof-comment-end               "}%"
 proof-comment-start-regexp	 "%[%{\t\n\f]"
 proof-comment-end		 ""
 ;; FIXME: these don't apply?
 proof-goal-command-regexp       "^%theorem"
 proof-save-command-regexp       "" ;; FIXME: empty?
 proof-goal-with-hole-regexp     "^%theorem\w-+\\(.*\\)\w-+:"
 proof-save-with-hole-regexp     "" ;; FIXME
 ;; proof-non-undoables-regexp      "undo\\|back"
 proof-goal-command              "%theorem %s."
 proof-save-command              "%prove "
 ;; proof-kill-goal-command         "Goal \"PROP no_goal_set\";"

;; proof-showproof-command         "pr()"
;; proof-undo-n-times-cmd          "pg_repeat undo %s;"
 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "Twelf.OS.chDir \"%s\";"
;; proof-shell-prompt-pattern      "[ML-=#>]+>? "
;; proof-shell-interrupt-regexp    "Interrupt"
;; proof-shell-start-goals-regexp  "Level [0-9]"
;; proof-shell-end-goals-regexp    "val it"
 
 ;; FIXME!
 ;; proof-shell-annotated-prompt-regexp "^\\(val it = () : unit\n\\)?ML>? "
 proof-shell-error-regexp        "%% ABORT %%"
 proof-shell-quit-cmd            "quit."
 proof-shell-restart-cmd	 "reset."

 ;; proof-shell-init-cmd  
 ;; "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 ;; proof-shell-proof-completed-regexp "^No subgoals!"
 ;; proof-shell-eager-annotation-start   
 ;;"^\\[opening \\|^###\\|^Reading")
 )

(provide 'twelf)