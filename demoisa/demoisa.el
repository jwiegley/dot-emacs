;; demoisa.el Example Proof General instance for Isabelle
;;
;; Copyright (C) 1999 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;;
;; =================================================================
;;
;; This is a much-whittled down version of Isabelle Proof General,
;; supplied as an (almost) minimal demonstration of how to instantiate
;; Proof General to a particular proof assistant.  It uses the plain
;; xterm interface of Isabelle, to demonstrate that hacking the proof
;; assistant is not necessary to get basic features working.
;;
;; This mode really works!  You you get a toolbar, menus, short-cut
;; keys, script management, a function menu, ability to run proof
;; assistant remotely, etc, etc.
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
;; (I've called this instance "Isabelle Demo Proof General" just to
;; avoid confusion with the real "Isabelle Proof General" in case the
;; demo gets loaded by accident).

(require 'proof)			; load generic parts


;; ======== User settings for Isabelle ========
;;
;; Defining variables using customize is pretty easy.
;; You should do it at least for your user options.
;;
;; proof-site provides use with two customization groups
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

(defcustom isabelledemo-prog-name "isabelle"
  "*Name of program to run Isabelle."
  :type 'file
  :group 'isabelledemo)

(defcustom isabelledemo-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelledemo-config)

(defcustom isabelledemo-not-undoable-commands-regexp
  "undo\\|back"
  "Regular expression matching commands which are *not* undoable."
  :type 'regexp
  :group 'isabelledemo-config)

;;
;; ======== Configuration of generic modes ========
;;

(defun demoisa-config ()
  "Configure Proof General scripting for Isabelle."
  (setq
   ;; proof script syntax
   proof-terminal-char		?\;	; ends every command
   proof-comment-start		"(*"
   proof-comment-end		"*)"

   ;; Next four used for function-menu and recognizing goal..save
   ;; regions in script buffer.
   ;; Isabelle has many (unbounded!) possible forms, we
   ;; only match one form here.  
   proof-goal-command-regexp    "^Goal"
   proof-save-command-regexp    "^qed"
   proof-goal-with-hole-regexp  "^Goal \"%s\""
   proof-save-with-hole-regexp  "^qed \"%s\""

   ;; proof engine commands
   proof-showproof-command	"pr()"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-kill-goal-command	"Goal \"PROP no_goal_set\";"

   ;; command hooks
   proof-goal-command-p		'demoisa-goal-command-p
   proof-count-undos-fn		'demoisa-count-undos
   proof-find-and-forget-fn	'demoisa-find-and-forget
   proof-goal-hyp-fn		'demoisa-goal-hyp
   proof-state-preserving-p	'demoisa-state-preserving-p

   ;; For the help menu
   proof-assistant-home-page	isabelledemo-web-page

   ;; Self-referential variable that's used to find
   ;; buffers in the scripting mode.
   proof-mode-for-script	'demoisa-proofscript-mode))


(defun demoisa-shell-config ()
  "Configure Proof General shell for Isabelle."
  (setq
   proof-shell-first-special-char	?\350

   ;; 
   proof-shell-annotated-prompt-regexp   "^\\(val it = () : unit\n\\)?ML>? "

   ;; cd command makes proof assistant follow directory of
   ;; current proof script (in case of included files).
   proof-shell-cd-cmd			"cd \"%s\""

   ;; This pattern is just for interaction in comint (shell buffer).
   ;; You don't need to set it.
   proof-shell-prompt-pattern		"[ML-=#>]+>? "

   proof-shell-interrupt-regexp         "Interrupt"
   proof-shell-error-regexp		"\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   
   proof-shell-start-goals-regexp	"\n"
   proof-shell-end-goals-regexp		""

   proof-shell-proof-completed-regexp
   (concat proof-shell-start-goals-regexp
	   "\\(\\(.\\|\n\\)*\nNo subgoals!\n\\)"
	   proof-shell-end-goals-regexp)

   ;; init-command sent on startup
   proof-shell-init-cmd                 "version;"
   proof-shell-quit-cmd			"quit();"

   ;; "urgent" messages displayed by Isabelle are highlighted in the
   ;; respoonse buffer, by matching with these regexps.
   proof-shell-eager-annotation-start   "^\\[opening \\|^###\\|^Reading\\|"
   proof-shell-eager-annotation-end     "]$\\|)$"))



;;
;; ======== Defining the derived modes ========
;;

;; The name of the script mode is always <proofsym>-script,
;; but the others can be whatever you like.
;;
;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.
;;

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
;;
;; A more sophisticated instantiation might set font-lock-keywords to
;; add highlighting, or some of the proof by pointing markup
;; configuration for the goals buffer.


;; The final piece of magic here is a hook which configures
;; the bare minimum to get the proof shell running.  
;; Proof General needs to know the name of the program to
;; run, and the modes for the shell, response, and goals buffers.

(add-hook 'proof-pre-shell-start-hook 'demoisa-pre-shell-start)

(defun demoisa-pre-shell-start ()
  (setq proof-prog-name		isabelledemo-prog-name)
  (setq proof-mode-for-shell    'demoisa-shell-mode)
  (setq proof-mode-for-response 'demoisa-response-mode)
  (setq proof-mode-for-pbp	'demoisa-goals-mode))



;;
;; ======== Hook functions used above ========
;;
;;
;; Code here has to be written specifically for each prover.
;;
;; There are four hook functions: count-undos, find-and-forget,
;;

;;
;; 1. count-undos
;;
;; This calculates undo operations within a proof. 
;;
(defun demoisa-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let 
      ((case-fold-search nil)
       (ct 0) str i)
    (if (and span (prev-span span 'type)
	     (not (eq (span-property (prev-span span 'type) 'type) 'comment))
	     (demoisa-goal-command-p
	      (span-property (prev-span span 'type) 'cmd)))
	(concat "choplev 0" proof-terminal-string)
      (while span
	(setq str (span-property span 'cmd))
	(cond ((eq (span-property span 'type) 'vanilla)
	       (or (proof-string-match isabelledemo-not-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property span 'type) 'pbp)
	       ;; this case probably redundant for Isabelle, unless
	       ;; we think of some nice ways of matching non-undoable
	       ;; commands.
	       (cond ((not (proof-string-match isabelledemo-not-undoable-commands-regexp str))
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq span (next-span span 'type)))
      (concat "ProofGeneral.repeat_undo " (int-to-string ct) proof-terminal-string))))

(defun demoisa-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match demoisa-goal-command-regexp str)) ; this regexp defined in demoisa-syntax.el

;;
;; 2. find-and-forget
;;
;; This calculates undo operations outwith a proof.  If we retract
;; before a "Goal" command, proof-kill-goal-command is sent, followed
;; by whatever is calculated by this function.
;;
;; Isabelle has no concept of a linear context, and you can happily
;; redeclare values in ML.  So forgetting back to the declaration of a
;; particular something makes no real sense.  
;; The function is given a trivial implementation in this case.
;;
;; Find LEGO or Coq's implementation of this function to see how to
;; write it for proof assistants that can do this.

(defun demoisa-find-and-forget (span)
  proof-no-command)


;; Parse proofstate output.  Isabelle does not display
;; named hypotheses in the proofstate output:  they
;; appear as a list in each subgoal.  Ignore
;; that aspect for now and just return the
;; subgoal number.
(defun demoisa-goal-hyp ()
  (if (looking-at proof-shell-goal-regexp)
      (cons 'goal (match-string 1))))

(defun demoisa-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (not (proof-string-match isabelledemo-not-undoable-commands-regexp cmd)))



(provide 'demoisa)
