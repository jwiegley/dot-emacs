(require 'proof)			; load generic parts

;; Adjust toolbar entries.  (Must be done
;; before proof-toolbar is loaded).

(if proof-running-on-XEmacs (setq af2-toolbar-entries
      (remassoc 'context af2-toolbar-entries)))


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

(defcustom af2-prog-name "af2 -pg"
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

(defcustom af2-doc-dir 
  "/usr/local/doc/af2"
  "The name of the root documentation directory for af2."
  :type 'string
  :group 'af2-config)

(defcustom af2-lib-dir 
  "/usr/local/lib/af2"
  "The name of the root directory for af2 libraries."
  :type 'string
  :group 'af2-config)

(defcustom af2-tags-program 
  (concat af2-doc-dir "/tools/af2_etags.sh")
  "Program to run to generate TAGS table for proof assistant."
  :type 'string
  :group 'af2-config)

(defcustom af2-tags-doc 
  t
  "*If non nil, tags table for af2 text documentation is loaded."
  :type 'boolean
  :group 'af2-config)

(defcustom af2-etags 
  (concat af2-doc-dir "/tools/af2_etags.sh")
  "Command to build tags table."
  :type 'string
  :group 'af2-config)

(require 'af2-tags)
(require 'af2-outline)
(require 'af2-font)
(require 'af2-fun)

;; ----- Af2 specific menu

(defpgdefault menu-entries
  '(    
    ["Delete symbol around cursor" af2-delete-symbol-around-point t]
    ["Delete symbol" af2-delete-symbol t]
    ["Compile theorem under cursor" af2-compile-theorem-around-point t]
    "----"
    ("Tags"
     ["create a tags table for local buffer" af2-tags-create-local-table t]
     ["------------------" nil nil]
;    ["load table" af2-tags-load-table t]
     ["add table"               af2-tags-add-table       t]
     ["add local table"         af2-tags-add-local-table t]
     ["add table for libraries" af2-tags-add-lib-table   t]
     ["add table for text doc"  af2-tags-add-doc-table   t]
     ["reset tags table list"   af2-tags-reset-table     t]
     ["------------------" nil nil]
     ["Find theorem, definition ..." find-tag t]
     ["complete theorem, definition ..." complete-tag t]
     )
    ))

;;
;; ======== Configuration of generic modes ========
;;

(defun af2-config ()
  "Configure Proof General scripting for Af2."
  (setq
   proof-terminal-char		?\.	; ends every command
   proof-script-command-end-regexp "[.][ \n\t\r]"
   proof-comment-start             "(*"
   proof-comment-end               "*)"
   proof-state-command             "goals."
   proof-goal-command-regexp       "goal\\|prop\\|proposition\\|lem\\|lemma\\|fact\\|cor\\|corollary\\|theo\\|theorem"
   proof-save-command-regexp       "save"
   proof-goal-with-hole-regexp     "\\(prop\\|proposition\\|lem\\|lemma\\|fact\\|cor\\|corollary\\|theo\\|theorem\\)[ \n\t\r]+\\([^ \n\t\r]+\\)"
   proof-save-with-hole-regexp     "save[ \n\t\r]+\\(\\([^ \n\t\r]+\\)\\)[ \n\t\r]*\.[ \n\t\r]"
   proof-shell-error-regexp        "^\\([^ \n\t\r]* \\)?\\(e\\|E\\)rror"
   proof-non-undoables-regexp      "undo"
   proof-goal-command              "goal %s."
   proof-save-command              "save %s."
   proof-kill-goal-command         "abort."
   proof-showproof-command         "goals."
   proof-undo-n-times-cmd          "undo %s."
   proof-find-and-forget-fn        'af2-find-and-forget
   proof-find-theorems-command      "search \"%s\"."
   proof-auto-multiple-files       nil
   font-lock-keywords              af2-font-lock-keywords 
   )
)

(defun af2-shell-config ()
  "Configure Proof General shell for Af2."
  (setq
   ;proof-shell-cd-cmd              "cd \"%s\""
   proof-shell-prompt-pattern      "\\(>af2> \\)\\|\\(%af2% \\)"
   proof-shell-annotated-prompt-regexp  "\\(>af2> \\)\\|\\(%af2% \\)"
   proof-shell-interrupt-regexp    "Interrupt"
   proof-shell-start-goals-regexp  "^Goals left to prove:"
   proof-shell-quit-cmd            "quit."
   proof-shell-restart-cmd         "quit."
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
    (proof-config-done)
    (af2-setup-outline)
    (define-key af2-mode-map [(control j)] 
      'proof-assert-next-command-interactive)
    (define-key af2-mode-map [(control c) (meta d)] 
      'af2-delete-symbol-around-point)  
    ;; Configure syntax table for block comments
    (modify-syntax-entry ?\* ". 23")
    (modify-syntax-entry ?\( "()1")
    (modify-syntax-entry ?\) ")(4"))

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


