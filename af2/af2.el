(require 'proof)			; load generic parts
(require 'sym-lock)

;; ======== User settings for Af2 ========
;;
;; Defining variables using customize is pretty easy.
;; You should do it at least for your prover-specific user options.
;;
;; proof-site provides us with two customization groups
;; automatically:  (based on the name of the assistant)
;;
;; 'af2        -  User options for Af2 Proof General
;; 'af2-config -  Configuration of Af2 Proof General
;;			   (constants, but may be nice to tweak)
;;
;; The first group appears in the menu
;;   ProofGeneral -> Customize -> Af2 
;; The second group appears in the menu:
;;   ProofGeneral -> Internals -> Af2 config
;;

(defcustom af2-prog-name "/home/raffalli/af2-all/af2/src/af2opt -pg"
  "*Name of program to run Af2."
  :type 'file
  :group 'af2)

(defcustom af2-sym-lock t
  "*Whether to use sym-lock or not."
  :type 'boolean
  :group 'af2)

(defcustom af2-web-page
  "http://www.lama.univ-savoie.fr/~RAFFALLI/af2.html"
  "URL of web page for Af2."
  :type 'string
  :group 'af2-config)


;;
;; ======== Configuration of generic modes ========
;;
(defconst af2-font-lock-keywords
  (list
;commands
   '("(\\*\\([^*]\\|\\*+[^*)]\\)*\\(\\*+)\\|\\**$\\)"
    0 'font-lock-comment-face t)
   '("\"\\([^\\\"]\\|\\\\.\\)*\""
    0 'font-lock-string-face t)
    (cons (concat "\\([ \t]\\|^\\)\\("
       "\\(Cst\\)\\|"
       "\\(Import\\)\\|"
       "\\(Use\\)\\|"
       "\\(Sort\\)\\|"
       "\\(new_\\(\\(intro\\)\\|\\(elim\\)\\|\\(rewrite\\)\\)\\)\\|"
       "\\(a\\("
       (concat
	"\\(dd_path\\)\\|"
	"\\(uthor\\)"
	"\\)\\)\\|")
       "\\(c\\("
       (concat
	"\\(laim\\)\\|"
	"\\(ose_def\\)"
	"\\)\\)\\|")
       "\\(d\\(\\(e\\(f\\|l\\)\\)\\|\\(ocuments\\)\\|\\(epend\\)\\)\\)\\|"
       "\\(e\\("
       (concat 
	"\\(lim_after_intro\\)\\|"
	"\\(xport\\)\\|"
	"\\(del\\)\\|"
	"\\(show\\)"
	"\\)\\)\\|")
       "\\(flag\\)\\|"
       "\\(goal\\)\\|"
       "\\(in\\("
       (concat
	"\\(clude\\)\\|"
	"\\(stitute\\)"
	"\\)\\)\\|")
       "\\(p\\(\\(ath\\)\\|\\(r\\(\\(int_sort\\)\\|\\(iority\\)\\)\\)\\)\\)\\|"
       "\\(quit\\)\\|"
       "\\(s\\(\\(ave\\)\\|\\(earch\\)\\)\\)\\|"
       "\\(t\\(" 
       (concat
	"\\(ex\\(_syntax\\)?\\)\\|"
	"\\(itle\\)"
	"\\)\\)")
       "\\)[ \t.]")
      '(0 'font-lock-keyword-face t))
;proof command
    (cons (concat "\\([ \t]\\|^\\)\\("
       "\\(a\\("
       (concat
	"\\(bort\\)\\|"
	"\\(bsurd\\)\\|"
	"\\(pply\\)\\|"
	"\\(xiom\\)"
	"\\)\\)\\|")
       "\\(constraints\\)\\|"
       "\\(elim\\)\\|"
       "\\(from\\)\\|"
       "\\(goals\\)\\|"
       "\\(in\\("
       (concat
	"\\(tros?\\)\\|"
	"\\(stance\\)"
	"\\)\\)\\|")
       "\\(l\\("
       (concat
	"\\(ocal\\)\\|"
	"\\(efts?\\)"
	"\\)\\)\\|")
       "\\(next\\)\\|"
       "\\(r\\(\\(ewrite\\(_hyp\\)?\\)\\|\\(ename\\)\\|\\(mh\\)\\)\\)\\|"
       "\\(slh\\)\\|"
       "\\(trivial\\)\\|" 
       "\\(u\\("       
       (concat
	"\\(se\\)\\|"
	"\\(ndo\\)\\|"
	"\\(nfold\\(_hyp\\)?\\)\\)\\)") 
       "\\)[ \t.]")
      '(0 'font-lock-type-face t))))

;; to change this table, xfd -fn '-adobe-symbol-*--12-*' may be
;; used to determine the symbol character codes.
(defvar af2-sym-lock-keywords
  '((">=" 0 1 179)
    ("<=" 0 1 163)
    ("!=" 0 1 185)
    (":<" 0 1 206)
    ("[^:]\\(:\\)[^:=]" 1 7 206)
    ("\\\\/" 0 1 36)
    ("/\\\\" 0 1 34)
    ("\\<or\\>" 0 3 218) 
    ("&" 0 1 217) 
    ("<->" 0 1 171)
    ("-->" 0 1 222)
    ("->" 0 1 174)
    ("~" 0 1 216))
  "If non nil: Overrides default Sym-Lock patterns for Af2.")

(defun af2-sym-lock-start ()
	(if (and (featurep 'sym-lock) af2-sym-lock)
	    (progn
	      (setq sym-lock-color
		    (face-foreground 'font-lock-function-name-face))
	      (if (not sym-lock-keywords)
		  (sym-lock af2-sym-lock-keywords)))))

(defun af2-config ()
  "Configure Proof General scripting for Af2."
  (setq
   proof-terminal-char		?\.	; ends every command
   proof-script-command-end-regexp "[.]\\($\\| \\|\\t\\)"
   proof-comment-start             "(*"
   proof-comment-end               "*)"
   proof-goal-command-regexp       "^goal"
   proof-save-command-regexp       "^save"
   proof-goal-with-hole-regexp     "\\(prop\\|proposition\\|lem\\|lemma\\|fact\\|cor\\|corollary\\|theo\\|theorem\\)\\([^ ]*\\)"
   proof-save-with-hole-regexp     "save \\(\\([^ ]*\\)\\)"
   proof-shell-error-regexp        "^[^ ]* \\(e\\|E\\)rror"
   proof-non-undoables-regexp      "undo"
   proof-goal-command              "goal %s."
   proof-save-command              "save %s."
   proof-kill-goal-command         "abort."
   proof-showproof-command         "goals."
   proof-undo-n-times-cmd          "undo %s."
   proof-auto-multiple-files       t
   font-lock-keywords              af2-font-lock-keywords 
 ))

(defun af2-shell-config ()
  "Configure Proof General shell for Af2."
  (setq
   ;proof-shell-cd-cmd              "cd \"%s\""
   proof-shell-prompt-pattern      "\\(>af2> \\)\\|\\(%af2% \\)"
   proof-shell-annotated-prompt-regexp  "\\(>af2> \\)\\|\\(%af2% \\)"
   proof-shell-interrupt-regexp    "Interrupt"
   proof-shell-start-goals-regexp  "^START GOALS"
   proof-shell-end-goals-regexp    "^END GOALS"
   proof-shell-quit-cmd            "quit."
   proof-shell-proof-completed-regexp   "^.*^proved"
))



;;
;; ======== Defining the derived modes ========
;;

;; The name of the script mode is always <proofsym>-script,
;; but the others can be whatever you like.
;;
;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.

(define-derived-mode af2-mode proof-mode
    "Af2 script" nil
    (af2-config)
    (af2-sym-lock-start)
    (proof-config-done))

(define-derived-mode af2-shell-mode proof-shell-mode
   "Af2 shell" nil
   (af2-shell-config)
   (proof-shell-config-done))

(define-derived-mode af2-response-mode proof-response-mode
  "Af2 response" nil
  (proof-response-config-done))

(define-derived-mode af2-goals-mode pbp-mode
  "Af2 goals" nil
  (af2-sym-lock-start)
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

(add-hook 'proof-pre-shell-start-hook 'af2-pre-shell-start)

(defun af2-pre-shell-start ()
  (setq proof-prog-name		af2-prog-name)
  (setq proof-mode-for-shell    'af2-shell-mode)
  (setq proof-mode-for-response 'af2-response-mode)
  (setq proof-mode-for-pbp	'af2-goals-mode))

(provide 'af2)


