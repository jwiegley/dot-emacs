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
  '("qed" "qed_spec_mp")
  ;; Related commands, but having different types, so PG
  ;; won't bother support them:
  ;; "result" "uresult" "bind_thm" "store_thm"
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

(defconst isa-tacticals '("REPEAT" "THEN" "ORELSE" "TRY" "ALLGOALS"))


;; ----- regular expressions

(defconst isa-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isa-idx (concat isa-id "\\(\\.[0-9]+\\)?"))

(defconst isa-ids (proof-ids isa-id "[ \t]*")
  "Matches a sequence of identifiers separated by whitespace.")

(defconst isar-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")

(defun isa-binder-regexp (binder dot)
    (concat binder "\\s-*\\(" isa-ids "\\)\\s-*" dot))

(defvar isa-font-lock-terms
  ;(list
   ;; This font lock regexp is faulty: causes big delay in
   ;; font locking any buffer with % something in it.
   ;; In any case, all Isabelle terms are in strings in
   ;; proof scripts and theory files, unfortunately, so
   ;; it has no use anyway.
   ;; lambda binders
   ; (list (isa-binder-regexp "\%" "\\.") 1 'proof-declaration-name-face))
  nil
  "*Font-lock table for Isabelle terms.")

(defconst isa-save-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-save)))

;; CHECKED
(defconst isa-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp isa-keywords-save)
	  "\\)\\s-+\"\\(" isa-id "\\)\"\\s-*;"))

(defcustom isa-goal-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp isa-keywords-goal))
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

(defvar isa-font-lock-keywords-1
   (append
    isa-font-lock-terms
    (list
     (cons (proof-ids-to-regexp isa-keywords) 'font-lock-keyword-face)
     (cons (proof-ids-to-regexp isa-tacticals) 'proof-tacticals-name-face)

     (list isa-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list isa-save-with-hole-regexp 2 'font-lock-function-name-face))))


;;
;; Configuration for output from Isabelle process
;;

(defun isa-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  ;; copied from above
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
  (modify-syntax-entry ?\) ")(4")
  ;; ignore strings so font-locking works
  ;; inside them
  (modify-syntax-entry ?\" " "))

(defvar isa-output-font-lock-terms
  (list
   (cons (concat "\351" isa-id "\350") 'proof-declaration-name-face)    ; class
   (cons (concat "\352'" isa-id "\350") 'proof-tacticals-name-face)     ; tfree
   (cons (concat "\353\\?'" isa-idx "\350") 'font-lock-type-face)       ; tvar
   (cons (concat "\354" isa-id "\350") 'font-lock-keyword-face)         ; free
   (cons (concat "\355" isa-id "\350") 'font-lock-keyword-face)         ; bound
   (cons (concat "\356" isa-idx "\350") 'font-lock-function-name-face)  ; var
   )
  "*Font-lock table for output from the Isabelle process.")


(provide 'isa-syntax)
