;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Author: Thomas Kleymann and Healfdene Goguen
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;; Please let us know if you could maintain this package!

;; $Id$

(require 'proof-syntax)

;; ----- keywords for font-lock.

(defvar coq-keywords-decl
  '(
"Axiom"
"Hypothesis"
"Parameter"
"Variable"
))

(defvar coq-keywords-defn
  '(
"CoFixpoint"
"CoInductive"
"Fixpoint"
"Inductive"
"Mutual\\s-+Inductive"
"Scheme"
))

(defvar coq-keywords-goal
  '(
"Definition"
"Fact"
"Goal"
"Lemma"
"Local"
"Remark"
"Theorem"
))

(defvar coq-keywords-save
  '(
"Defined"
"Save"
"Qed"
))

(defvar coq-keywords-kill-goal '(
"Abort"
))

(defvar coq-keywords-commands
  '(
"AddPath"
"Cd"
"Check"
"Class"
"Coercion"
"DelPath"
"Eval"
"Extraction"
"Focus"
"Immediate"
"Hint"
"Infix"
"Opaque"
"Print"
"Proof"
"Pwd"
"Reset"
"Search"
"Show"
"Transparent"
))

(defvar coq-tactics
  '(
"Absurd"
"Apply"
"Assumption"
"Auto"
"Case"
"Change"
"Clear"
"Cofix"
"Compute"
"Constructor"
"Contradiction"
"Cut"
"DHyp"
"DInd"
"Dependent"
"Destruct"
"Discriminate"
"Double"
"EApply"
"EAuto"
"Elim"
"End"
"Exact"
"Exists"
"Fix"
"Generalize"
"Grammar"
"Hnf"
"Induction"
"Injection"
"Intro"
"Intros"
"Intuition"
"Inversion_clear"
"Inversion"
"LApply"
"Left"
"Linear"
"Load"
"Pattern"
"Program_all"
"Program"
"Prolog"
"Realizer"
"Red"
"Reflexivity"
"Replace"
"Rewrite"
"Right"
"Section"
"Simplify_eq"
"Simpl"
"Specialize"
"Split"
"Symmetry"
"Syntax"
"Tauto"
"Transitivity"
"Trivial"
"Unfold"
))

(defvar coq-keywords
  (append coq-keywords-goal coq-keywords-save coq-keywords-decl
	  coq-keywords-defn coq-keywords-commands coq-tactics)
  "All keywords in a Coq script")

(defvar coq-tacticals '(
"Do"
"Idtac"
"OrElse"
"Repeat"
"Try"
))

;; ----- regular expressions
(defvar coq-error-regexp "^\\(Error\\|Discarding\\|Syntax error\\|System Error\\)"
  "A regular expression indicating that the Coq process has identified
  an error.")

(defvar coq-id proof-id)

(defvar coq-ids (proof-ids coq-id))

(defun coq-abstr-regexp (paren char)
    (concat paren "\\s-*\\(" coq-ids "\\)\\s-*" char))

(defvar coq-font-lock-terms
  (list

   ;; lambda binders
   (list (coq-abstr-regexp "\\[" ":") 1 ''proof-declaration-name-face)

   ;; Pi binders
   (list (coq-abstr-regexp "(" ":") 1 ''proof-declaration-name-face)
   
   ;; Kinds
   (cons (concat "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\s-*\\(("
		   coq-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Coq terms.")

;; According to Coq, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see coq-global-p.
(defconst coq-save-command-regexp
  (concat "^" (proof-ids-to-regexp coq-keywords-save)))
(defconst coq-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-save)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*\."))
(defconst coq-goal-command-regexp
  (concat "^" (proof-ids-to-regexp coq-keywords-goal)))
(defconst coq-goal-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-goal)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*:"))
(defconst coq-decl-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-decl)
	  "\\)\\s-+\\(" coq-ids "\\)\\s-*:"))
(defconst coq-defn-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-defn)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*[:[]"))

(defvar coq-font-lock-keywords-1
   (append
    coq-font-lock-terms
    (list
     (cons (proof-ids-to-regexp coq-keywords) 'font-lock-keyword-face)
     (cons (proof-ids-to-regexp coq-tacticals) ''proof-tacticals-name-face)

     (list coq-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-decl-with-hole-regexp 2 ''proof-declaration-name-face)
     (list coq-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-save-with-hole-regexp 2 'font-lock-function-name-face))))

(provide 'coq-syntax)
