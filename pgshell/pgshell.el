;; pgshell.el - Proof General for shell scripts.
;;
;; David Aspinall.  $Id$
;;
;; This instance of PG is handy just for using script management to
;; cut-and-paste into a buffer running an ordinary shell of some kind.
;;
;; I'm providing this so that tool demonstrators may use it instead of
;; tediously doing cut-and-paste of commands from a file.  Nothing
;; to do with theorem proving really!
;;
;; To use this instance of PG, visit a file with the ".pgsh" extension.
;; 
;; Feedback welcome.


(require 'proof-easy-config)           
(require 'proof-syntax)

(proof-easy-config  'pgshell	"PG-Shell"
 proof-prog-name		 "/bin/sh" ;; or choose your shell
 proof-terminal-char             ?\;	   ;; better: parse the syntax
 proof-script-comment-start      "\#"
 proof-shell-annotated-prompt-regexp  "^.*[$] $" ;; matches shell prompts
 ;; next settings are just to prevent warnings
 proof-save-command-regexp	proof-no-regexp
 )

(provide 'pgshell)
