;; --------------------------------------------------------------------
;; Copyright (c) - 2012--2016 - IMDEA Software Institute
;; Copyright (c) - 2012--2016 - Inria
;;
;; Distributed under the terms of the GPL-v3 license
;; --------------------------------------------------------------------

(require 'proof-syntax)
(require 'easycrypt-keywords)
(require 'easycrypt-hooks)

(defconst easycrypt-id "[A-Za-z_]+")

(defconst easycrypt-terminal-string    ".")
(defconst easycrypt-command-end-regexp "[^\\.]\\.\\(\\s \\|\n\\|$\\)")

(defconst easycrypt-keywords-proof-goal '("lemma" "equiv" "hoare" "realize"))
(defconst easycrypt-keywords-proof-save '("save" "qed"))

(defconst easycrypt-non-undoables-regexp "^pragma\\b")

(defconst easycrypt-keywords-code-open  '("{"))
(defconst easycrypt-keywords-code-close '("}")) 
(defconst easycrypt-keywords-code-end   '(";"))

(defvar easycrypt-other-symbols "\\(\\.\\.\\|\\[\\]\\)")

(defvar easycrypt-operator-char-1 "=\\|<\\|>\\|~")
(defvar easycrypt-operator-char-2 "\\+\\|\\-")
(defvar easycrypt-operator-char-3 "\\*\\|/\\|%")
(defvar easycrypt-operator-char-4 "!\\|\\$\\|&\\|\\?\\|@\\|\\^\\|:\\||\\|#")

(defvar easycrypt-operator-char-1234
  (concat "\\(" easycrypt-operator-char-1
          "\\|" easycrypt-operator-char-2
		  "\\|" easycrypt-operator-char-3
		  "\\|" easycrypt-operator-char-4
          "\\)"))

(defconst easycrypt-proof-save-regexp
  (concat "^\\(" (proof-ids-to-regexp easycrypt-keywords-proof-save) "\\)\\b"))

(defconst easycrypt-goal-command-regexp
  (concat "^\\(?:local\\s-+\\)?\\(?:" (proof-ids-to-regexp easycrypt-keywords-proof-goal) "\\)"
          "\\s-+\\(?:nosmt\\s-+\\)?\\(\\sw+\\)"))

(defun easycrypt-save-command-p (span str)
  "Decide whether argument is a [save|qed] command or not"
  (let ((txt (or (span-property span 'cmd) "")))
       (proof-string-match-safe easycrypt-proof-save-regexp txt)))

(defun easycrypt-goal-command-p (span)
  "Is SPAN a goal start?"
  (let ((txt (or (span-property span 'cmd) "")))
       (proof-string-match-safe easycrypt-goal-command-regexp txt)))

(defun easycrypt-init-output-syntax-table ()
  "Set appropriate values for syntax table for EasyCrypt output."
  (modify-syntax-entry ?,   " ")
  (modify-syntax-entry ?\'  "_")
  (modify-syntax-entry ?_   "_")

  ;; For comments
  (modify-syntax-entry ?\* ". 23") 

  ;; For blocks
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){")
  (modify-syntax-entry ?\[ "(]")
  (modify-syntax-entry ?\] ")["))

;; ----- regular expressions

(defvar easycrypt-error-regexp "^\\[error-[0-9]+-[0-9]+\\]\\|^anomaly"
  "A regexp indicating that the EasyCrypt process has identified an error.")

(defvar easycrypt-shell-proof-completed-regexp "No more goals"
  "*Regular expression indicating that the proof has been completed.")

(defconst easycrypt-any-command-regexp
  ;; allow terminator to be considered as command start:
  ;; FIXME: really needs change in generic function to take account of this,
  ;; since the end character of a command is not the start
  (concat "\\(\\s(\\|\\s)\\|\\sw\\|\\s \\|\\s_\\)*="  ;match assignments
          "\\|;;\\|;\\|" 
          (proof-ids-to-regexp easycrypt-global-keywords))
  "Regexp matching any EasyCrypt command start or the terminator character.")

(defconst easycrypt-keywords-indent-open
  (append (append '("local") easycrypt-keywords-proof-goal)
          easycrypt-keywords-code-open))

(defconst easycrypt-keywords-indent-close
  (append easycrypt-keywords-proof-save
          easycrypt-keywords-code-close))

(defconst easycrypt-keywords-indent-enclose
  (append easycrypt-keywords-code-open
          easycrypt-keywords-code-close
          easycrypt-keywords-code-end
          easycrypt-keywords-proof-goal
          easycrypt-keywords-proof-save))

; Regular expression for indentation
(defconst easycrypt-indent-any-regexp
  (proof-regexp-alt easycrypt-any-command-regexp "\\s(" "\\s)"))
    
(defconst easycrypt-indent-enclose-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-enclose) "\\s)"))

(defconst easycrypt-indent-open-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-open) "\\s("))

(defconst easycrypt-indent-close-regexp
  (proof-regexp-alt (proof-ids-to-regexp easycrypt-keywords-indent-close) "\\s)"))

(defface easycrypt-tactics-closing-face
  (proof-face-specs
   (:foreground "red")
   (:foreground "red")
   ())
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)

(defface easycrypt-tactics-dangerous-face
  (proof-face-specs
   (:background "red")
   (:background "red")
   ())
  "Face for names of dangerous tactics in proof scripts."
  :group 'proof-faces)

(defface easycrypt-tactics-tacticals-face
  (proof-face-specs
   (:foreground "dark green")
   (:foreground "dark green")
   ())
  "Face for names of tacticals in proof scripts."
  :group 'proof-faces)

(defconst easycrypt-tactics-closing-face   'easycrypt-tactics-closing-face)
(defconst easycrypt-tactics-dangerous-face 'easycrypt-tactics-dangerous-face)
(defconst easycrypt-tactics-tacticals-face 'easycrypt-tactics-tacticals-face)

(defvar easycrypt-font-lock-keywords
  (list
    (cons (proof-ids-to-regexp easycrypt-global-keywords)    'font-lock-keyword-face)
    (cons (proof-ids-to-regexp easycrypt-tactic-keywords)    'proof-tactics-name-face)
    (cons (proof-ids-to-regexp easycrypt-tactical-keywords)  'easycrypt-tactics-tacticals-face)
    (cons (proof-ids-to-regexp easycrypt-bytac-keywords)     'easycrypt-tactics-closing-face)
    (cons (proof-ids-to-regexp easycrypt-dangerous-keywords) 'easycrypt-tactics-dangerous-face)
    (cons (proof-ids-to-regexp easycrypt-prog-keywords)      'font-lock-keyword-face)
    (cons (concat easycrypt-operator-char-1234 "+")          'font-lock-type-face)
    (cons easycrypt-other-symbols                            'font-lock-type-face)))

(defun easycrypt-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?_  "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\. ".")
  (modify-syntax-entry ?\* ". 23n")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(provide 'easycrypt-syntax)
