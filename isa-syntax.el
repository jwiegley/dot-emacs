;; isa-syntax.el Syntax expressions for Isabelle
;;

(require 'proof-syntax)

;; ----- keywords for font-lock.

(defvar isa-keywords-decl
  '(
))

(defvar isa-keywords-defn
  '(
"bind_thm"
))

(defvar isa-keywords-goal
  '(
"goal"
))

(defvar isa-keywords-save
  '(
"qed"
))

(defvar isa-keywords-kill-goal '(
))

(defvar isa-keywords-commands
  '(
"by"
"goal"
))

;; See isa-command-table in Isamode/isa-menus.el to get this list.
(defvar isa-tactics
  '(
"resolve_tac" "assume_tac"
))

(defvar isa-keywords
  (append isa-keywords-goal isa-keywords-save isa-keywords-decl
	  isa-keywords-defn isa-keywords-commands isa-tactics)
  "All keywords in a Isa script")

(defvar isa-tacticals '(
"REPEAT" "THEN" "ORELSE" "TRY"
))

;; ----- regular expressions

;; this should come from isa-ml-compiler stuff.
(defvar isa-error-regexp 
  "^.*Error:"
  "A regular expression indicating that the Isa process has identified
  an error.")

(defvar isa-id proof-id)

(defvar isa-ids (proof-ids isa-id))

(defun isa-abstr-regexp (paren char)
    (concat paren "\\s-*\\(" isa-ids "\\)\\s-*" char))

(defvar isa-font-lock-terms
  (list

   ;; lambda binders
   (list (isa-abstr-regexp "\\[" ":") 1 'font-lock-declaration-name-face)

   ;; Pi binders
   (list (isa-abstr-regexp "(" ":") 1 'font-lock-declaration-name-face)
   
   ;; Kinds
   (cons (concat "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\s-*\\(("
		   isa-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Isa terms.")

;; According to Isa, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see isa-global-p.
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
