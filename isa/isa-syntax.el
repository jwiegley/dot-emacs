;; isa-syntax.el Syntax expressions for Isabelle
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Isabelle maintainer <isabelle@dcs.ed.ac.uk>
;;
;; $Id$
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

;(defgroup isa-scripting nil
;  "Customization of Isabelle script management"
;  :group 'external
;  :group 'languages)

;(defgroup isa-syntax nil
;  "Customization of Isabelle's syntax recognition"
;  :group 'isa-scripting)

;; ----- syntax for font-lock and other features

;; FIXME: this command-keyword orientation isn't  good
;;  enough for Isabelle, since we can have arbitrary
;;  ML code around.  One solution is to define a
;;  restricted language consisting of the interactive
;;  commands.  We'd still need regexps below, though.
;;  Alternatively: customize this for Marcus Wenzel's 
;;  proof language.


(defgroup isa-syntax nil
  "Customization of Isabelle syntax for proof mode"
  :group 'isa-settings)

(defcustom isa-keywords-decl
  '("val" "fun" "datatype"
    "signature" "structure")
  "Isabelle keywords for declarations.  Includes ML keywords to fontify ML files."
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-defn
  '("bind_thm")
  "Isabelle keywords for definitions"
  :group 'isa-syntax
  :type '(repeat string))

;; isa-keywords-goal is used to manage undo actions
(defcustom isa-keywords-goal
  '("Goal" "Goalw" "goal" "goalw" "goalw_cterm")
  "Isabelle commands to begin an interactive proof"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-save
  '("qed" "result" "uresult" "bind_thm" "store_thm")
    "Isabelle commands to extract the proved theorem"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-commands
  '("by" "byev"
    "ba" "br" "be" "bd" "brs" "bes" "bds"
    "chop" "choplev" "back" "undo"
    "fa" "fr" "fe" "fd" "frs" "fes" "fds"
    "bw" "bws" "ren"
    ;; batch proofs
    "prove_goal" "qed_goal" "prove_goalw" "qed_goalw" "prove_goalw_cterm")
  "Isabelle command keywords"
  :group 'isa-syntax
  :type '(repeat string))

;; See isa-command-table in Isamode/isa-menus.el to get this list.
;; BUT: tactics are not commands, so appear inside some expression.
(defconst isa-tactics
  '("resolve_tac" "assume_tac"))

;; NB: this means that any adjustments above by customize will
;; only have effect in next session.
(defconst isa-keywords
  (append isa-keywords-goal isa-keywords-save isa-keywords-decl
	  isa-keywords-defn isa-keywords-commands isa-tactics)
  "All keywords in a Isabelle script")

(defconst isa-tacticals '("REPEAT" "THEN" "ORELSE" "TRY"))

;; ----- regular expressions

;; this should come from isa-ml-compiler stuff.
(defcustom isa-error-regexp 
  "^.*Error:\\|^\\*\\*\\*\\|^\\#\\#\\#"
  "A regexp indicating that Isabelle has identified an error."
  :type 'string
  :group 'isa-syntax)

(defconst isa-id proof-id)

(defconst isa-ids (proof-ids isa-id))

(defun isa-abstr-regexp (paren char)
    (concat paren "\\s-*\\(" isa-ids "\\)\\s-*" char))

(defvar isa-font-lock-terms
  (list
   ;; lambda binders
   (list (concat "\%\\s-*\\(" isa-ids "\\)\\.") 1
	 'font-lock-declaration-name-face)

   ;; Pi binders
   (list (isa-abstr-regexp "(" ":") 1 'font-lock-declaration-name-face)
   
   ;; Kinds
   (cons (concat "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\s-*\\(("
		   isa-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Isa terms.")

(defconst isa-save-command-regexp
  (concat "^" (ids-to-regexp isa-keywords-save)))
(defconst isa-save-with-hole-regexp
  (concat "\\(" (ids-to-regexp isa-keywords-save)
	  "\\)\\s-+\\(" isa-id "\\)\\s-*\."))
(defconst isa-goal-command-regexp
  (concat "^" (ids-to-regexp isa-keywords-goal)))
(defconst isa-goal-with-hole-regexp
  (concat "\\(" (ids-to-regexp isa-keywords-goal)
	  "\\)\\s-+\\(" isa-id "\\)\\s-*:"))
(defconst isa-decl-with-hole-regexp
  (concat "\\(" (ids-to-regexp isa-keywords-decl)
	  "\\)\\s-+\\(" isa-ids "\\)\\s-*:"))
(defconst isa-defn-with-hole-regexp
  (concat "\\(" (ids-to-regexp isa-keywords-defn)
	  "\\)\\s-+\\(" isa-id "\\)\\s-*[:[]"))

(defvar isa-font-lock-keywords-1
   (append
    isa-font-lock-terms
    (list
     (cons (ids-to-regexp isa-keywords) 'font-lock-keyword-face)
     (cons (ids-to-regexp isa-tacticals) 'font-lock-tacticals-name-face)

     (list isa-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list isa-decl-with-hole-regexp 2 'font-lock-declaration-name-face)
     (list isa-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (list isa-save-with-hole-regexp 2 'font-lock-function-name-face))))

(provide 'isa-syntax)
