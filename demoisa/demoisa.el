;; demoisa.el Example Proof General instance for Isabelle
;;
;; Copyright (C) 1999 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; =================================================================
;;
;;		Isabelle Proof General in 30 setqs
;;
;; This is a whittled down version of Isabelle Proof General, supplied
;; as an (almost) minimal demonstration of how to instantiate Proof
;; General to a particular proof assistant.  You can use this as a
;; template to get support for a new assistant going.
;;
;; This mode uses the unadulterated terminal interface of Isabelle, to
;; demonstrate that hacking the proof assistant is not necessary to
;; get basic features working.
;;
;; And it really works!  You you get a toolbar, menus, short-cut keys,
;; script management for multiple files, a function menu, ability to
;; run proof assistant remotely, etc, etc.
;;
;; To try it out, set in the shell PROOFGENERAL_ASSISTANTS=demoisa
;; before invoking Emacs.  (Of course, you need Isabelle installed).
;;
;; What's missing? 
;;
;;  1. A few handy commands (e.g. proof-find-theorems-command)
;;  2. Syntax settings and highlighting for proof scripts
;;  3. Indentation for proof scripts
;;  4. Special markup characters in output for robustness 
;;  5. True script management for multiple files (automatic mode is used)
;;  6. Proof by pointing
;;
;; How easy is it to add all that?
;;
;;  1. Trivial.  2. A table specifying syntax codes for characters
;;  (strings, brackets, etc) and some regexps; depends on complexity
;;  of syntax.  3. A bit of elisp to scan script; depends on
;;  complexity of syntax.  4. Needs hacking in the proof assistant:
;;  how hard is to hack your assistant to do this?  5. Depends on file
;;  management mechanism in the prover, may need hacking there to send
;;  messages. But automatic multiple files may be all you need anyway.
;;  6. Non trivial (but worth a go).
;;
;;
;; =================================================================
;;
;;
;; Basic configuration is controlled by one line in `proof-site.el'.
;; It has this line in proof-assistant-table:
;;
;;     (demoisa "Isabelle Demo"	"\\.ML$")
;;
;; From this it loads this file "demoisa/demoisa.el" whenever
;; a .ML file is visited, and sets the mode to `demoisa-mode'
;; (defined below).  
;; 
;; I've called this instance "Isabelle Demo Proof General" just to
;; avoid confusion with the real "Isabelle Proof General" in case the
;; demo gets loaded by accident.
;;
;; To make the line above take precedence over the real Isabelle mode
;; later in the table, set PROOFGENERAL_ASSISTANTS=demoisa in the
;; shell before starting Emacs  (or customize proof-assistants).
;;


(require 'proof)			; load generic parts


;; ======== User settings for Isabelle ========
;;
;; Defining variables using customize is pretty easy.
;; You should do it at least for your prover-specific user options.
;;
;; proof-site provides us with two customization groups
;; automatically:  (based on the name of the assistant)
;;
;; 'isabelledemo        -  User options for Isabelle Demo Proof General
;; 'isabelledemo-config -  Configuration of Isabelle Proof General
;;			   (constants, but may be nice to tweak)
;;
;; The first group appears in the menu
;;   ProofGeneral -> Customize -> Isabelledemo 
;; The second group appears in the menu:
;;   ProofGeneral -> Internals -> Isabelledemo config
;;

(defcustom isabelledemo-prog-name "isabelle"
  "*Name of program to run Isabelle."
  :type 'file
  :group 'isabelledemo)

(defcustom isabelledemo-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelledemo-config)


;;
;; ======== Configuration of generic modes ========
;;

(defun demoisa-config ()
  "Configure Proof General scripting for Isabelle."
  (setq
   proof-terminal-char		?\;	; ends every command
   proof-comment-start		"(*"
   proof-comment-end		"*)"
   proof-goal-command-regexp    "^Goal"
   proof-save-command-regexp    "^qed"
   proof-goal-with-hole-regexp  "^Goal \\(\\(\"%s\"\\)\\)"
   proof-save-with-hole-regexp  "^qed \\(\\(\"%s\"\\)\\)"
   proof-non-undoables-regexp   "undo\\|back"
   proof-undo-n-times-cmd	"pg_repeat undo %s;"
   proof-showproof-command	"pr()"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-kill-goal-command	"Goal \"PROP no_goal_set\";"
   proof-assistant-home-page	isabelledemo-web-page
   proof-auto-multiple-files    t))


(defun demoisa-shell-config ()
  "Configure Proof General shell for Isabelle."
  (setq
   proof-shell-annotated-prompt-regexp   "^\\(val it = () : unit\n\\)?ML>? "
   proof-shell-cd-cmd			"cd \"%s\""
   proof-shell-prompt-pattern		"[ML-=#>]+>? "
   proof-shell-interrupt-regexp         "Interrupt"
   proof-shell-error-regexp		"\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   proof-shell-start-goals-regexp	"Level [0-9]"
   proof-shell-end-goals-regexp		"val it"
   proof-shell-proof-completed-regexp   "\\(\\(.\\|\n\\)*No subgoals!\n\\)"
   proof-shell-eager-annotation-start   "^\\[opening \\|^###\\|^Reading"
   proof-shell-init-cmd  ; define a utility function, in a lib somewhere?
   "fun pg_repeat f 0 = () 
      | pg_repeat f n = (f(); pg_repeat f (n-1));"
   proof-shell-quit-cmd			"quit();"))



;;
;; ======== Defining the derived modes ========
;;

;; The name of the script mode is always <proofsym>-script,
;; but the others can be whatever you like.
;;
;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.

(define-derived-mode demoisa-mode proof-mode
    "Isabelle Demo script" nil
    (demoisa-config)
    (proof-config-done))

(define-derived-mode demoisa-shell-mode proof-shell-mode
   "Isabelle Demo shell" nil
   (demoisa-shell-config)
   (proof-shell-config-done))

(define-derived-mode demoisa-response-mode proof-response-mode
  "Isabelle Demo response" nil
  (proof-response-config-done))

(define-derived-mode demoisa-goals-mode pbp-mode
  "Isabelle Demo goals" nil
  (proof-goals-config-done))

;; The response buffer and goals buffer modes defined above are
;; trivial.  In fact, we don't need to define them at all -- they
;; would simply default to "proof-response-mode" and "pbp-mode".

;; A more sophisticated instantiation might set font-lock-keywords to
;; add highlighting, or some of the proof by pointing markup
;; configuration for the goals buffer.

;; The final piece of magic here is a hook which configures settings
;; to get the proof shell running.  Proof General needs to know the
;; name of the program to run, and the modes for the shell, response,
;; and goals buffers.

(add-hook 'proof-pre-shell-start-hook 'demoisa-pre-shell-start)

(defun demoisa-pre-shell-start ()
  (setq proof-prog-name		isabelledemo-prog-name)
  (setq proof-mode-for-shell    'demoisa-shell-mode)
  (setq proof-mode-for-response 'demoisa-response-mode)
  (setq proof-mode-for-pbp	'demoisa-goals-mode))

(provide 'demoisa)
