;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Author: Thomas Kleymann and Healfdene Goguen
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 2.0  1998/09/09 13:57:04  da
;; Fixup branch number
;;
;; Revision 1.1  1998/09/03 13:51:13  da
;; Renamed for new subdirectory structure
;;
;; Revision 2.0  1998/08/11 14:59:53  da
;; New branch
;;
;; Revision 1.2  1998/08/11 11:43:13  da
;; Renamed <file>-fontlock to <file>-syntax
;;
;; Revision 1.14  1998/06/11 12:20:14  hhg
;; Added "Scheme" as definition keyword.
;;
;; Revision 1.13  1998/06/10 11:38:04  hhg
;; Added "Mutual Inductive" as definition keyword.
;; Changed "\\s " into "\\s-" as whitespace pattern.
;;
;; Revision 1.12  1998/06/03 18:01:54  hhg
;; Changed Compute from command to tactic.
;; Added Fix, Destruct and Cofix as tactics.
;; Added Local as goal.
;;
;; Revision 1.11  1998/06/02 15:33:16  hhg
;; Minor modifications to comments
;;
;; Revision 1.10  1998/05/15 16:13:23  hhg
;; Added CoFixpoint and tactics.
;; Changed indentation.
;;
;; Revision 1.9  1998/05/05 14:19:39  hhg
;; Added CoInductive.
;; Made updates to reflect problem with "Definition", which couldn't be
;; used with proof scripts.
;;
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
   (list (coq-abstr-regexp "\\[" ":") 1 'font-lock-declaration-name-face)

   ;; Pi binders
   (list (coq-abstr-regexp "(" ":") 1 'font-lock-declaration-name-face)
   
   ;; Kinds
   (cons (concat "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\s-*\\(("
		   coq-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Coq terms.")

;; According to Coq, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see coq-global-p.
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
	  "\\)\\s-+\\(" coq-ids "\\)\\s-*:"))
(defconst coq-defn-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-defn)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*[:[]"))

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

(provide 'coq-syntax)
