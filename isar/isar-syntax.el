;; isar-syntax.el Syntax expressions for Isabelle/Isar
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id isar-syntax.el,v 2.14 1998/11/03 14:41:54 da Exp$
;;

(require 'proof-syntax)

;;; Proof mode customization: how should it work?
;;;   Presently we have a bunch of variables in proof.el which are
;;;   set from a bunch of similarly named variables in <engine>-syntax.el.
;;;
;;;   Seems a bit daft: why not just have the customization in
;;;   one place, and settings hardwired in <engine>-syntax.el.
;;;
;;;   That way we can see which settings are part of instantiation of
;;;   proof.el, and which are part of cusomization for <engine>.

;; ------ customize groups

;(defgroup isar-scripting nil
;  "Customization of Isabelle/Isar script management"
;  :group 'external
;  :group 'languages)

;(defgroup isar-syntax nil
;  "Customization of Isabelle/Isar's syntax recognition"
;  :group 'isar-scripting)

;; ----- syntax for font-lock and other features

(defgroup isar-syntax nil
  "Customization of Isabelle/Isar syntax for proof mode"
  :group 'isar-settings)

;MMW FIXME This stuff should be generated automatically (and made logic specific).
;MMW FIXME Tune these categories.
;MMW FIXME Can I invent new categories?

(defcustom isar-keywords-begin-theory
  '(
    "update_context"
    "theory"
    "context"
    )
  "Isabelle/Isar keywords begin theory commands."
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-end-theory
  '(
    "end"
    )
  "Isabelle/Isar keywords end theory commands."
  :group 'isar-syntax
  :type '(repeat string))


(defcustom isar-keywords-diag
  '()
  "Isabelle/Isar keywords diagnostic commands."
  :group 'isar-syntax
  :type '(repeat string))



(defcustom isar-keywords-decl
  '(
    "use_thy"
    "use" 
    "undos"
    "undo"
    "types"
    "typedecl"
    "typed_print_translation"
    "typ"
    "translations"
    "top"
    "token_translation"
    "title"
    "thm"
    "text"
    "term"
    "syntax"
    "subsubsection"
    "subsection"
    "setup"
    "section"
    "rep_datatype"
    "redos"
    "redo"
    "record"
    "recdef"
    "quit"
    "pwd"
    "prop"
    "print_translation"
    "print_theory"
    "print_theorems"
    "print_syntax"
    "print_methods"
    "print_facts"
    "print_binds"
    "print_attributes"
    "print_ast_translation"
    "primrec"
    "pr"
    "path"
    "parse_translation"
    "parse_ast_translation"
    "oracle"
    "nonterminals"
    "local"
    "load"
    "kill_proof"
    "inductive"
    "help"
    "global"
    "exit"
    "defaultsort"
    "datatype"
    "consts"
    "commit"
    "constdefs"
    "coinductive"
    "classrel"
    "classes"
    "chapter"
    "cd"
    "axioms"
    "axclass"
    "arities"
    "ML"
    )
  "Isabelle/Isar keywords for declarations."
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-defn
  '(
    "theorems"
    "lemmas"
    "defs"
    "axclass"
    )
  "Isabelle/Isar keywords for definitions"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-goal
  '(
    "typedef"
    "theorem"
    "lemma"
    "instance"
    )
  "Isabelle/Isar commands to begin an interactive proof"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-save
  '(
    "qed_with"
    "qed"
    "by"
    "\\.\\."
    "\\."
    )
  "Isabelle/Isar commands finish a top-level proof and store the theorem"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-kill-goal
  '("kill")
  "Isabelle/Isar kill command keywords"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-minor
  '(
    "and"
    "as"
    "binder"
    "infixl"
    "infixr"
    "is"
    "output"
    )
  "Isabelle/Isar minor keywords"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-proof-commands
  '(
;    "qed"
    "proof" 
    "next"
;    "by"
;    "\\.\\."
;    "\\."
    )
  "Isabelle/Isar proof command keywords"
  :group 'isar-syntax
  :type '(repeat string))

(defcustom isar-keywords-commands
  '(
    "up"
    "thus"
    "then_refine"
    "then"
    "show"
    "refine"
    "prev"
    "note"
    "let"
    "hence"
    "have"
    "from"
    "fix"
    "back"
    "assume"
    "{{"
    "}}"
    )
  "Isabelle/Isar command keywords"
  :group 'isar-syntax
  :type '(repeat string))


;; NB: this means that any adjustments above by customize will
;; only have effect in next session.
(defconst isar-keywords
  (append isar-keywords-diag isar-keywords-goal isar-keywords-save
	  isar-keywords-decl isar-keywords-defn isar-keywords-commands)
  "All keywords in a Isabelle/Isar theory")


;; ----- regular expressions

(defconst isar-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isar-idx (concat isar-id "\\(\\.[0-9]+\\)?"))

(defconst isar-ids (proof-ids isar-id "[ \t]*")
  "Matches a sequence of identifiers separated by whitespace.")

;;FIXME
(defconst isar-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")
;;(defconst isar-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"\\|{|\\(\\([^|]\\||[^}]\\)*\\)|}")
;;(defconst isar-string "{|\\([^|]*\\)|}")

(defconst isar-string-regexp
  (concat "\\s-*" isar-string "\\s-*")
  "Regexp matching Isabelle/Isar strings, with contents bracketed.")

(defvar isar-font-lock-terms
  (list
   (cons (concat "\351" isar-id "\350") 'proof-declaration-name-face)    ; class
   (cons (concat "\352'" isar-id "\350") 'proof-tacticals-name-face)     ; tfree
   (cons (concat "\353\\?'" isar-idx "\350") 'font-lock-type-face)       ; tvar
   (cons (concat "\354" isar-id "\350") 'font-lock-function-face)        ; free
   (cons (concat "\355" isar-id "\350") 'font-lock-keyword-face)         ; bound
   (cons (concat "\356" isar-idx "\350") 'font-lock-function-face)       ; var
   )
  "*Font-lock table for Isabelle terms.")

(defconst isar-save-command-regexp
  (concat "^" (proof-ids-to-regexp isar-keywords-save)))

; FIXME ?
;(defconst isar-save-with-hole-regexp
;  (concat "\\(" (proof-ids-to-regexp isar-keywords-save) isar-string-regexp "\\)"))
;(defconst isar-save-with-hole-regexp
;  (concat "\\(qed_with\\)\\s*:\\s*" isar-string-regexp))

(defconst isar-save-with-hole-regexp "^FIXME$\\(\\)")

(defcustom isar-goal-command-regexp
  (proof-ids-to-regexp isar-keywords-goal)
  "Regular expression used to match a goal."
  :type 'regexp
  :group 'isabelle-isar-config)

;; MMW FIXME ??
(defconst isar-goal-with-hole-regexp
  (concat "\\("
	  (proof-ids-to-regexp isar-keywords-goal)
	  "\\)" isar-string-regexp)
  "Regexp matching goal commands in Isabelle/Isar which name a theorem")

(defvar isar-font-lock-keywords-1
  (append
   isar-font-lock-terms
   (list
    (cons (proof-ids-to-regexp isar-keywords-proof-commands) 'font-lock-function-name-face)
    (cons (proof-ids-to-regexp isar-keywords) 'font-lock-keyword-face)
    (cons (proof-ids-to-regexp isar-keywords-minor) 'font-lock-type-face)
    (list isar-goal-with-hole-regexp 2 'font-lock-function-name-face)
    (list isar-save-with-hole-regexp 2 'font-lock-function-name-face))))

(provide 'isar-syntax)
