;; isa-syntax.el Syntax expressions for Isabelle
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;;
;; FIXME: the syntax needs checking carefully, and splitting
;; into output vs input syntax.
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

;; ----- character syntax

(defun isa-init-syntax-table ()
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
  (modify-syntax-entry ?.  "w")
  (modify-syntax-entry ?_  "w")
  (modify-syntax-entry ?\' "w")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(defun isa-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  (isa-init-syntax-table)
  ;; ignore strings so font-locking works
  ;; inside them
  (modify-syntax-entry ?\" " "))


;; ----- syntax for font-lock and other features

;; FIXME: this command-keyword orientation isn't  good
;;  enough for Isabelle, since we can have arbitrary
;;  ML code around.  One solution is to define a
;;  restricted language consisting of the interactive
;;  commands.  We'd still need regexps below, though.
;;  Alternative 1: customize this for Markus Wenzel's 
;;  proof language.  Markus has done this now!
;;  Alternative 2: add hooks from Isabelle to say
;;  "I've just seen a goal command" or "I've just seen a
;;  tactic".  This would allow more accurate 
;; counting of undos.

;; FIXME da:  here are some examples of input failures I've
;; found in real proofs:
;;
;;   val lemma = result() RS spec RS mp;
;;
;; Not recognized as a qed command, and therefore assumed 
;; to be an undoable tactic command.
;;

(defgroup isa-syntax nil
  "Customization of Isabelle syntax for proof mode"
  :group 'isa-settings)

(defcustom isa-keywords-decl
  '("val" "fun" "datatype" "signature" "structure")
  "Isabelle keywords for declarations.  Includes ML keywords to fontify ML files."
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-defn
  '("bind_thm" "bind_thms")
  "Isabelle keywords for definitions"
  :group 'isa-syntax
  :type '(repeat string))

;; isa-keywords-goal is used to manage undo actions
(defcustom isa-keywords-goal
  '("Goal" "Goalw" "goal" "goalw" "goalw_cterm" "atomic_goal" "atomic_goalw")
  "Isabelle commands to begin an interactive proof"
  :group 'isa-syntax
  :type '(repeat string))

(defcustom isa-keywords-save
  '("qed" "qed_spec_mp" "no_qed" "result()" "result ()")
  ;; Related commands, but having different types, so PG
  ;; won't bother support them:
  ;; "uresult" "bind_thm" "store_thm"
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

;; NB: this means that any adjustments above by customize will
;; only have effect in next session.
(defconst isa-keywords
  (append isa-keywords-goal isa-keywords-save isa-keywords-decl
	  isa-keywords-defn isa-keywords-commands)
  "All keywords in a Isabelle script")

;; The most common Isabelle/Pure tacticals
(defconst isa-tacticals
  '("ALLGOALS" "DETERM" "EVERY" "EVERY'" "FIRST" "FIRST'" "FIRSTGOAL"
    "ORELSE" "ORELSE'" "REPEAT" "REPEAT" "REPEAT1" "REPEAT_FIRST"
    "REPEAT_SOME" "SELECT_GOAL" "SOMEGOAL" "THEN" "THEN'" "TRY" "TRYALL"))


;; ----- regular expressions

(defconst isa-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isa-idx (concat isa-id "\\(\\.[0-9]+\\)?"))

(defconst isa-ids (proof-ids isa-id "[ \t]*")
  "Matches a sequence of identifiers separated by whitespace.")

(defconst isa-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")

(defconst isa-save-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-save)))

;; CHECKED
(defconst isa-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp isa-keywords-save)
	  "\\)\\s-+\"\\(" isa-id "\\)\"\\s-*;"))

(defcustom isa-goal-command-regexp
  (proof-regexp-alt
   (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-goal))
   ;; match val ... = goal blah
   (proof-anchor-regexp
    (concat
     (proof-ids-to-regexp '("val")) ".+=\\s-*"
     "\\(" (proof-ids-to-regexp isa-keywords-goal) "\\)")))
  "Regular expression used to match a goal."
  :type 'regexp
  :group 'isabelle-config)

(defconst isa-string-regexp
  (concat "\\s-*\"\\(" isa-id "\\)\"\\s-*")
  "Regexp matching ML strings, with contents bracketed.")

(defconst isa-goal-with-hole-regexp
  (concat "\\("
	  ;; Don't bother with "val xxx = prove_goal blah".
	  (proof-ids-to-regexp '("qed_goal"))
	  "\\)" isa-string-regexp)
  "Regexp matching goal commands in Isabelle which name a theorem")


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
     (:foreground "blue"))
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


(defvar isa-font-lock-keywords-1
  (list
   (cons (proof-ids-to-regexp isa-keywords) 'font-lock-keyword-face)
   (cons (proof-ids-to-regexp isa-tacticals) 'proof-tacticals-name-face)
   (list isa-goal-with-hole-regexp 2 'font-lock-function-name-face)
   (list isa-save-with-hole-regexp 2 'font-lock-function-name-face)))

(defvar isa-output-font-lock-keywords-1
  (list
   (cons (concat "\351" isa-id "\350") 'isabelle-class-name-face)
   (cons (concat "\352'" isa-id "\350") 'isabelle-tfree-name-face)
   (cons (concat "\353\\?'" isa-idx "\350") 'isabelle-tvar-name-face)
   (cons (concat "\354" isa-id "\350") 'isabelle-free-name-face)
   (cons (concat "\355" isa-id "\350") 'isabelle-bound-name-face)
   (cons (concat "\356" isa-idx "\350") 'isabelle-var-name-face)
   (cons (concat "\357" isa-idx "\350") 'proof-declaration-name-face)
   )
  "*Font-lock table for Isabelle terms.")


(provide 'isa-syntax)
