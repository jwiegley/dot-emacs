;; coq-fontlock.el Font lock expressions for Coq
;; Copyright (C) 1997 LFCS Edinburgh. 
;; Author: Thomas Kleymann and Healfdene Goguen
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 1.8  1998/01/15 13:30:17  hhg
;; Added coq-shell-cd
;; Some new fontlocks
;;
;; Revision 1.7  1997/11/26 17:12:55  hhg
;; Incorporated tms's suggestion for simplifying coq-font-lock-keywords-1
;;
;; Revision 1.6  1997/11/06 16:46:20  hhg
;; Updates to Coq fontlock tables
;;
;; Revision 1.5  1997/10/30 15:58:29  hhg
;; Updates for coq, including:
;; 	* pbp-goal-command and pbp-hyp-command use proof-terminal-string
;; 	* updates to keywords
;; 	* fix for goal regexp
;;
;; Revision 1.4  1997/10/24 14:51:07  hhg
;; Changed order of "Inversion_clear" and "Inversion" so that former is
;; fontified first.
;; Added "Print" to list of commands.
;;
;; Revision 1.3  1997/10/17 14:45:53  hhg
;; Added "Induction" as tactic
;;
;; Revision 1.2  1997/10/13 17:10:29  tms
;; *** empty log message ***
;;
;; Revision 1.1.2.2  1997/10/08 08:22:28  hhg
;; Updated undo, fixed bugs, more modularization
;;
;; Revision 1.1.2.1  1997/10/07 13:34:10  hhg
;; New structure to share as much as possible between LEGO and Coq.
;;
;;

(require 'proof-fontlock)

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
"Definition"
"Fixpoint"
"Inductive"
))

(defvar coq-keywords-goal
  '(
"Fact"
"Goal"
"Lemma"
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
"Compute"
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
"Constructor"
"Contradiction"
"Cut"
"DHyp"
"DInd"
"Dependent"
"Discriminate"
"Double"
"EApply"
"EAuto"
"Elim"
"End"
"Exact"
"Exists"
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
"Linear"
"Load"
"Pattern"
"Program"
"Prolog"
"Realizer"
"Red"
"Reflexivity"
"Replace"
"Rewrite"
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

;; ----- regular expressions for font-lock
;; *** To update
(defvar coq-error-regexp "^\\(Error\\|Discarding\\|Syntax error\\|System Error\\)"
  "A regular expression indicating that the Coq process has
  identified an error.") 

(defvar coq-id proof-id)

;; *** To check: whether separator is just ,
(defvar coq-ids (proof-ids coq-id))

;; *** To update: from here down!
(defun coq-abstr-regexp (paren char)
    (concat paren "\\s *\\(" coq-ids "\\)\\s *" char))

(defvar coq-font-lock-terms
  (list

   ; lambda binders
     (list (coq-abstr-regexp "\\[" ":") 1 'font-lock-declaration-name-face)

     ; let binders
;;     (list (coq-decl-defn-regexp "=") 1 'font-lock-function-name-face)

     ; Pi binders
     (list (coq-abstr-regexp "(" ":") 1 'font-lock-declaration-name-face)
   
     ;; Kinds
     (cons (concat "\\<Prop\\>\\|\\<Type\\s *\\(("
		   coq-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Coq terms.")

(defconst coq-save-command-regexp
  (concat "^" (ids-to-regexp coq-keywords-save)))
(defconst coq-save-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-save)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*\."))
(defconst coq-goal-command-regexp
  (concat "^" (ids-to-regexp coq-keywords-goal)))
(defconst coq-goal-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-goal)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*:"))
(defconst coq-decl-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-decl)
	  "\\)\\s-*\\(" coq-id "\\)\\s-*:"))
(defconst coq-defn-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-defn)
	  "\\)\\s-*\\(" coq-id "\\)\\s-*[:[]"))

(defvar coq-font-lock-keywords-1
   (append
    coq-font-lock-terms
    (list
     (cons (ids-to-regexp coq-keywords) 'font-lock-keyword-face)
     (cons (ids-to-regexp coq-tacticals) 'font-lock-tacticals-name-face)

     (list coq-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-decl-with-hole-regexp 2 'font-lock-declaration-name-face)
     (list coq-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-save-with-hole-regexp 2 'font-lock-function-name-face))))

(provide 'coq-fontlock)
