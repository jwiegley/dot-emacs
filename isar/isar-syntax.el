;; isar-syntax.el Syntax expressions for Isabelle/Isar
;; Copyright (C) 1994-1998 LFCS Edinburgh.
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id$
;;

(require 'proof-syntax)
(require 'isar-keywords)

;; ----- character syntax

(defun isar-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ "w")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  "w")
  (modify-syntax-entry ?>  "w")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?.  "w")
  (modify-syntax-entry ?_  "w")
  (modify-syntax-entry ?\' "w")
  (modify-syntax-entry ??  "w")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
  (modify-syntax-entry ?\{ "(}1")
  (modify-syntax-entry ?\} "){4"))

(defun isar-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  (isar-init-syntax-table)
  ;; ignore strings so font-locking works
  ;; inside them
  (modify-syntax-entry ?\" " ")
  (modify-syntax-entry ?\* ".")
  (modify-syntax-entry ?\( "()")
  (modify-syntax-entry ?\) ")(")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){"))


;; ----- keyword groups

(defconst isar-keywords-theory-enclose
  (append isar-keywords-theory-begin
          isar-keywords-theory-switch
          isar-keywords-theory-end))

(defconst isar-keywords-theory
  (append isar-keywords-theory-heading
          isar-keywords-theory-decl
          isar-keywords-theory-goal))

(defconst isar-keywords-save
  (append isar-keywords-qed
          isar-keywords-qed-block
          isar-keywords-qed-global))

(defconst isar-keywords-proof-enclose
  (append isar-keywords-proof-block
          isar-keywords-proof-open
          isar-keywords-proof-close
          isar-keywords-qed-block))

(defconst isar-keywords-proof
  (append isar-keywords-proof-goal
          isar-keywords-proof-chain
          isar-keywords-proof-decl
          isar-keywords-qed))

(defconst isar-keywords-proof-context
  (append isar-keywords-proof-asm
          isar-keywords-proof-asm-goal))

(defconst isar-keywords-local-goal
  (append isar-keywords-proof-goal
          isar-keywords-proof-asm-goal))

(defconst isar-keywords-improper
  (append isar-keywords-theory-script
	  isar-keywords-proof-script
          isar-keywords-qed-global))

(defconst isar-keywords-outline
  isar-keywords-theory-heading)

(defconst isar-keywords-fume
  (append isar-keywords-theory-begin
          isar-keywords-theory-heading
          isar-keywords-theory-decl
          isar-keywords-theory-script
          isar-keywords-theory-goal))

(defconst isar-keywords-indent-open
  (append isar-keywords-theory-goal
          isar-keywords-proof-goal
          isar-keywords-proof-asm-goal
          isar-keywords-proof-open))

(defconst isar-keywords-indent-close
  (append isar-keywords-save
          isar-keywords-proof-close))

(defconst isar-keywords-indent-enclose
  (append isar-keywords-proof-block
          isar-keywords-proof-close
          isar-keywords-qed-block))


;; ----- regular expressions

;; tuned version of proof-ids-to-regexp --- admit single non-word char
;; as well (e.g. { })

(defun isar-ids-to-regexp (l)
  "Maps a non-empty list of tokens `l' to a regexp matching any element"
  (mapconcat
   (lambda (s) (if (string-match "^\\W$" s) s (concat "\\<" s "\\>")))
   l "\\|"))

(defconst isar-long-id-stuff "\\([A-Za-z0-9'_.]+\\)")

(defconst isar-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isar-idx (concat isar-id "\\(\\.[0-9]+\\)?"))

(defconst isar-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")

(defconst isar-any-command-regexp
  (isar-ids-to-regexp isar-keywords-major)
  "Regexp matching any Isabelle/Isar command keyword.")

(defconst isar-name-regexp
  (concat "\\s-*\\(" isar-string "\\|" isar-id "\\)\\s-*")
  "Regexp matching Isabelle/Isar names, with contents grouped.")

(defconst isar-tac-regexp
  "\\<[A-Za-z][A-Za-z0-9'_]*_tac\\>"
  "Regexp matching old-style tactic names")

(defconst isar-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-save)))

(defconst isar-global-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-qed-global)))

(defconst isar-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-goal)))

(defconst isar-local-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-local-goal)))

(defconst isar-comment-start "(*")
(defconst isar-comment-end "*)")
(defconst isar-comment-start-regexp (regexp-quote isar-comment-start))
(defconst isar-comment-end-regexp (regexp-quote isar-comment-end))

(defconst isar-string-start-regexp "\"\\|{\\*")
(defconst isar-string-end-regexp "\"\\|\\*}")


;; antiquotations

(defconst isar-antiq-regexp
  (concat "\\(@{\\([^\"{}]+\\|" isar-string "\\)\\{0,7\\}}\\)")
  "Regexp matching Isabelle/Isar antiquoations.")

(defun isar-match-antiq (limit)
  "Match Isabelle/Isar antiquotations."
  (or
   (and (proof-looking-at-syntactic-context)
	(proof-looking-at isar-antiq-regexp))
   (let (done ans)
     (while (not done)
       (if (proof-re-search-forward isar-antiq-regexp limit t)
	   (and (proof-looking-at-syntactic-context)
		(setq done t) (setq ans t))
	 (setq done t)))
     ans)))


;; ----- Isabelle inner syntax hilite

(defface isabelle-class-name-face
  '((((type x) (class color) (background light))
     (:foreground "red"))
    (((type x) (class color) (background dark))
     (:foreground "red3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tfree-name-face
  '((((type x) (class color) (background light))
     (:foreground "purple"))
    (((type x) (class color) (background dark))
     (:foreground "purple3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tvar-name-face
  '((((type x) (class color) (background light))
     (:foreground "purple"))
    (((type x) (class color) (background dark))
     (:foreground "purple3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-free-name-face
  '((((type x) (class color) (background light))
     (:foreground "blue"))
    (((type x) (class color) (background dark))
     (:foreground "blue3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-bound-name-face
  '((((type x) (class color) (background light))
     (:foreground "green4"))
    (((type x) (class color) (background dark))
     (:foreground "green"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-var-name-face
  '((((type x) (class color) (background light))
     (:foreground "darkblue"))
    (((type x) (class color) (background dark))
     (:foreground "blue3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defconst isabelle-class-name-face 'isabelle-class-name-face)
(defconst isabelle-tfree-name-face 'isabelle-tfree-name-face)
(defconst isabelle-tvar-name-face 'isabelle-tvar-name-face)
(defconst isabelle-free-name-face 'isabelle-free-name-face)
(defconst isabelle-bound-name-face 'isabelle-bound-name-face)
(defconst isabelle-var-name-face 'isabelle-var-name-face)

(defvar isar-font-lock-keywords-1
  (list
   (cons (isar-ids-to-regexp isar-keywords-minor)          'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-control)        'proof-error-face)
   (cons (isar-ids-to-regexp isar-keywords-diag)           'proof-tacticals-name-face)
   (cons (isar-ids-to-regexp isar-keywords-theory-enclose) 'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-theory)         'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-enclose)  'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-proof)          'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-context)  'proof-declaration-name-face)
   (cons (isar-ids-to-regexp isar-keywords-improper)       'font-lock-reference-face)
   (cons isar-tac-regexp 'font-lock-reference-face)
   '(isar-match-antiq (0 'font-lock-variable-name-face prepend))))

(defvar isar-output-font-lock-keywords-1
  (list
   (cons (concat "\351" isar-long-id-stuff "\350") 'isabelle-class-name-face)
   (cons (concat "\352'" isar-id "\350") 'isabelle-tfree-name-face)
   (cons (concat "\353\\?'" isar-idx "\350") 'isabelle-tvar-name-face)
   (cons (concat "\354" isar-id "\350") 'isabelle-free-name-face)
   (cons (concat "\355" isar-id "\350") 'isabelle-bound-name-face)
   (cons (concat "\356\\?" isar-idx "\350") 'isabelle-var-name-face)
   (cons (concat "\357" isar-id "\350") 'proof-declaration-name-face)
   (cons (concat "\357\\?" isar-idx "\350") 'proof-declaration-name-face))
  "*Font-lock table for Isabelle terms.")

(defvar isar-goals-font-lock-keywords
  (append
   (list
    "^theory "
    "^proof (prove):"
    "^proof (state):"
    "^proof (chain):"
    "^goal (theorem.*):"
    "^goal (lemma.*):"
    "^goal (have.*):"
    "^goal (show.*):"
    "^picking this:"
    "^using this:"
    "^this:"
    "^term bindings:"
    "^facts:"
    "^cases:"
    "^prems:"
    "^fixed variables:"
    "^type constraints:"
    "^default sorts:"
    "^used type variable names:"
    "^[Ff]lex-flex pairs:"
    "^[Cc]onstants:"
    "^[Vv]ariables:"
    "^[Tt]ype variables:"
    "^\\s-*[0-9][0-9]?\\. ")
   isar-output-font-lock-keywords-1)
  "*Font-lock table for Isabelle/Isar output.")


;; ----- variations on undo

(defconst isar-undo "undo;")
(defconst isar-kill "kill;")

(defun isar-remove (name)
  (concat "init_toplevel; kill_thy \"" name "\";"))

(defun isar-undos (i)
  (if (> i 0) (concat "undos_proof " (int-to-string i) ";")
    proof-no-command))

(defun isar-cannot-undo (cmd)
  (concat "cannot_undo \"" cmd "\";"))


(defconst isar-undo-fail-regexp
  (proof-anchor-regexp
   (isar-ids-to-regexp (append isar-keywords-control isar-keywords-theory-end))))

(defconst isar-undo-skip-regexp
  (proof-anchor-regexp (proof-regexp-alt (isar-ids-to-regexp isar-keywords-diag) ";")))

(defconst isar-undo-remove-regexp
  (concat
   (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-begin))
   isar-name-regexp))

(defconst isar-undo-kill-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-switch)))


;; ----- function-menu

(defconst isar-any-entity-regexp
  (concat "\\(" (isar-ids-to-regexp isar-keywords-fume) "\\)"
          "\\(" isar-name-regexp "[[:=]\\)?"))

(defconst isar-named-entity-regexp
  (concat "\\(" (isar-ids-to-regexp isar-keywords-fume) "\\)"
          isar-name-regexp "[[:=]"))

(defconst isar-unnamed-entity-regexp
  (concat "\\(" (isar-ids-to-regexp isar-keywords-fume) "\\)"))

(defconst isar-next-entity-regexps
  (list isar-any-entity-regexp
        (list isar-named-entity-regexp '(1 2))
        (list isar-unnamed-entity-regexp 1)))


;; ----- indentation

(defconst isar-indent-any-regexp
  (proof-regexp-alt isar-any-command-regexp "\\s(" "\\s)"))
(defconst isar-indent-inner-regexp
  (proof-regexp-alt "[[]()]"))
(defconst isar-indent-enclose-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-enclose) "\\s)"))
(defconst isar-indent-open-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-open) "\\s("))
(defconst isar-indent-close-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-close) "\\s)"))


;; ----- outline mode

(defconst isar-outline-regexp
  (concat "[ \t]*\\(" (isar-ids-to-regexp isar-keywords-outline) "\\)")
  "Outline regexp for Isabelle/Isar documents")

(defconst isar-outline-heading-end-regexp "\n")


(provide 'isar-syntax)
