;; coq-fontlock.el Font lock expressions for Coq
;; Copyright (C) 1997 LFCS Edinburgh. 
;; Author: Thomas Kleymann and Healfdene Goguen
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
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
"Hint"
"Infix"
"Opaque"
"Pwd"
"Reset"
"Search"
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
"Exact"
"Generalize"
"Hnf"
"Injection"
"Intro"
"Intros"
"Intuition"
"Inversion"
"LApply"
"Linear"
"Pattern"
"Program"
"Prolog"
"Realizer"
"Red"
"Reflexivity"
"Replace"
"Rewrite"
"Simpl"
"Simplify_eq"
"Specialize"
"Symmetry"
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
(defvar coq-error-regexp "^\\(Error\\|Syntax error\\)"
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

(defvar coq-font-lock-keywords-1
   (append
    coq-font-lock-terms
    (list
     (cons (ids-to-regexp coq-keywords) 'font-lock-keyword-face)
     (cons (ids-to-regexp coq-tacticals) 'font-lock-tacticals-name-face)

     (list (concat "\\("
		   (ids-to-regexp coq-keywords-goal)
		   "\\)\\s *\\(" coq-id "\\)\\s *:")
             2 'font-lock-function-name-face)

     (list (concat "\\("
		   (ids-to-regexp coq-keywords-decl)
		   "\\)\\s *\\(" coq-id "\\)\\s *:")
             2 'font-lock-declaration-name-face)

     (list (concat "\\("
		   (ids-to-regexp coq-keywords-defn)
		   "\\)\\s *\\(" coq-id "\\)\\s *:")
             2 'font-lock-function-name-face)

     (list (concat "\\("
		   (ids-to-regexp coq-keywords-save)
		   "\\)\\s *\\(" coq-id "\\)")
             2 'font-lock-function-name-face))))

(provide 'coq-fontlock)
