(require 'proof)			; load generic parts

;; Adjust toolbar entries.  (Must be done
;; before proof-toolbar is loaded).

(if proof-running-on-XEmacs (setq phox-toolbar-entries
      (remassoc 'context phox-toolbar-entries)))


;; ======== User settings for PhoX ========
;;
;; Defining variables using customize is pretty easy.
;; You should do it at least for your prover-specific user options.
;;
;; proof-site provides us with two customization groups
;; automatically:  (based on the name of the assistant)
;;
;; 'phox        -  User options for PhoX Proof General
;; 'phox-config -  Configuration of PhoX Proof General
;;			   (constants, but may be nice to tweak)
;;
;; The first group appears in the menu
;;   ProofGeneral -> Customize -> PhoX 
;; The second group appears in the menu:
;;   ProofGeneral -> Internals -> PhoX config
;;

(defcustom phox-prog-name "phox -pg"
  "*Name of program to run PhoX."
  :type 'file
  :group 'phox)

(defcustom phox-sym-lock t
  "*Whether to use sym-lock or not."
  :type 'boolean
  :group 'phox)

(defcustom phox-web-page
  "http://www.lama.univ-savoie.fr/~RAFFALLI/phox.html"
  "URL of web page for PhoX."
  :type 'string
  :group 'phox-config)

(defcustom phox-doc-dir 
  "/usr/local/doc/phox"
  "The name of the root documentation directory for PhoX."
  :type 'string
  :group 'phox-config)

(defcustom phox-lib-dir 
  "/usr/local/lib/phox"
  "The name of the root directory for PhoX libraries."
  :type 'string
  :group 'phox-config)

(defcustom phox-tags-program 
  (concat phox-doc-dir "/tools/phox_etags.sh")
  "Program to run to generate TAGS table for proof assistant."
  :type 'string
  :group 'phox-config)

(defcustom phox-tags-doc 
  t
  "*If non nil, tags table for PhoX text documentation is loaded."
  :type 'boolean
  :group 'phox-config)

(defcustom phox-etags 
  (concat phox-doc-dir "/tools/phox_etags.sh")
  "Command to build tags table."
  :type 'string
  :group 'phox-config)

(require 'phox-tags)
(require 'phox-outline)
(require 'phox-font)
(require 'phox-fun)

;; ----- PhoX specific menu

(defpgdefault menu-entries
  '(    
    ["Delete symbol around cursor" phox-delete-symbol-around-point t]
    ["Delete symbol" phox-delete-symbol t]
    ["Compile theorem under cursor" phox-compile-theorem-around-point t]
    "----"
    ("Tags"
     ["create a tags table for local buffer" phox-tags-create-local-table t]
     ["------------------" nil nil]
;    ["load table" phox-tags-load-table t]
     ["add table"               phox-tags-add-table       t]
     ["add local table"         phox-tags-add-local-table t]
     ["add table for libraries" phox-tags-add-lib-table   t]
     ["add table for text doc"  phox-tags-add-doc-table   t]
     ["reset tags table list"   phox-tags-reset-table     t]
     ["------------------" nil nil]
     ["Find theorem, definition ..." find-tag t]
     ["complete theorem, definition ..." complete-tag t]
     )
    ))

;;
;; ======== Configuration of generic modes ========
;;

(defun phox-config ()
  "Configure Proof General scripting for PhoX."
  (setq
   proof-terminal-char		?\.	; ends every command
   proof-script-command-end-regexp "[.]\\([ \t\n\r]\\)"
   proof-comment-start             "(*"
   proof-comment-end               "*)"
   proof-state-command             "goals."
   proof-goal-command-regexp       
   (concat
    "^"
    phox-comments-regexp
    "\\(goal\\|prop\\(osition\\)?\\|lem\\(ma\\)?\\|fact\\|cor\\(ollary\\)?\\|theo\\(rem\\)?\\)")
   proof-save-command-regexp       
   (concat
    "^"
    phox-comments-regexp
    "save")
   proof-goal-with-hole-regexp  
   (concat 
    "^"
    phox-comments-regexp
    "\\(prop\\(osition\\)?\\|lem\\(ma\\)?\\|fact\\|cor\\(ollary\\)?\\|theo\\(rem\\)?\\)"
    phox-strict-comments-regexp
    phox-ident-regexp)
   proof-goal-with-hole-result     16
   proof-save-with-hole-regexp     
   (concat 
    "^"
    
phox-comments-regexp
    "save"
    phox-strict-comments-regexp
    phox-ident-regexp)
   proof-save-with-hole-result     11
   proof-ignore-for-undo-count         
   (concat
    "^"
    phox-comments-regexp
    "\\(constraints\\|flag\\|goals\\|pri\\(nt\\(_sort\\)?\\|ority\\)\\|eshow\\|search\\|depend\\)")
   proof-non-undoables-regexp       
   (concat
    "^"
    phox-comments-regexp
    "\\(undo\\|abort\\)")
   proof-shell-error-regexp        "^\\([^ \n\t\r]* \\)?\\(\\(e\\|E\\)rror\\)\\|\\(\\(f\\|F\\)ailure\\)"
   proof-goal-command              "goal %s."
   proof-save-command              "save %s."
   proof-kill-goal-command         "abort."
   proof-showproof-command         "goals."
   proof-undo-n-times-cmd          "undo %s."
   proof-find-and-forget-fn        'phox-find-and-forget
   proof-find-theorems-command      "search \"%s\"."
   proof-auto-multiple-files       nil
   font-lock-keywords              phox-font-lock-keywords 
   )
)

(defun phox-shell-config ()
  "Configure Proof General shell for PhoX."
  (setq
   ;proof-shell-cd-cmd              "cd \"%s\""
   proof-shell-prompt-pattern      "\\(>phox> \\)\\|\\(%phox% \\)"
   proof-shell-annotated-prompt-regexp  "\\(>phox> \\)\\|\\(%phox% \\)"
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

(define-derived-mode phox-mode proof-mode
    "PhoX script" nil
    (phox-config)
    (phox-sym-lock-start)
    (proof-config-done)
    (phox-setup-outline)
    (define-key phox-mode-map [(control j)] 
      'phox-assert-next-command-interactive)
    ;; with the previous binding,
    ;; it is nice to do : xmodmap -e "keysym KP_Enter = Linefeed"

    (define-key phox-mode-map [(control c) (meta d)] 
      'phox-delete-symbol-around-point)  
    ;; Configure syntax table for block comments
    (modify-syntax-entry ?\* ". 23")
    (modify-syntax-entry ?\( "()1")
    (modify-syntax-entry ?\) ")(4"))

(define-derived-mode phox-shell-mode proof-shell-mode
   "PhoX shell" nil
   (phox-shell-config)
   (proof-shell-config-done))

(define-derived-mode phox-response-mode proof-response-mode
  "PhoX response" nil
  (setq 
   font-lock-keywords  phox-font-lock-keywords
   proof-output-fontify-enable     t)
  (phox-sym-lock-start)
  (proof-response-config-done)
  (font-lock-mode))

(define-derived-mode phox-goals-mode proof-goals-mode
  "PhoX goals" nil
  (setq 
   font-lock-keywords  phox-font-lock-keywords
   proof-output-fontify-enable     t)
  (phox-sym-lock-start)
  (proof-goals-config-done)
  (font-lock-mode))

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

(add-hook 'proof-pre-shell-start-hook 'phox-pre-shell-start)

(defun phox-pre-shell-start ()
  (setq proof-prog-name		phox-prog-name)
  (setq proof-mode-for-shell    'phox-shell-mode)
  (setq proof-mode-for-response 'phox-response-mode)
  (setq proof-mode-for-goals	'phox-goals-mode))

(provide 'phox)


