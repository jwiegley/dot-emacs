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

;; (require 'twelf-font)		; font lock configuration
;; (require 'twelf-old)			; port of parts of old code

;; FIXME: almost working, must modify syntax table so that comments
;; are recognized properly.

(proof-easy-config 
 'twelf "Twelf" 
 proof-prog-name		 "twelf-server"
 proof-assistant-home-page       "http://www.cs.cmu.edu/~twelf/"
 proof-terminal-char             ?\.
 proof-shell-auto-terminate-commands nil ; server commands don't end with .

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
 proof-shell-cd-cmd              "OS.chDir %s"
 proof-shell-prompt-pattern      "%% OK %%\n"
 proof-shell-interrupt-regexp    "interrupt"
;; proof-shell-start-goals-regexp  "Level [0-9]"
;; proof-shell-end-goals-regexp    "val it"

 proof-shell-annotated-prompt-regexp "%% [OA][KB]O?R?T? %%\n"
 proof-shell-error-regexp        "Server error:"
 proof-shell-quit-cmd            "quit"
 proof-shell-restart-cmd	 "reset"

 ;; unset
 ;; proof-shell-init-cmd  
 ;; "fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));"
 ;; proof-shell-proof-completed-regexp "^No subgoals!"
 ;; proof-shell-eager-annotation-start   
 ;;"^\\[opening \\|^###\\|^Reading")
 )

(provide 'twelf)