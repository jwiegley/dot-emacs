;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Authors: Thomas Kleymann and Healfdene Goguen
;; Maintainer: Patrick Loiseleur <Patrick.Loiseleur@lri.fr> 

;; $Id$

(require 'proof-syntax)

;; ----- keywords for font-lock.

(defvar coq-keywords-decl
  '(
"Axiom[s]?"
"Hypotheses"
"Hypothesis"
"Parameter[s]?"
;; da: 3.2 I added Section here, to try to fix undo for Sections working
;; better.  
"Section"				
"Variable[s]?"
"Global\\s-+Variable"
;;added tactic def here because it needs Reset to be undone correctly
"Tactic\\s-+Definition"
))

(defvar coq-keywords-defn
  '(
"CoFixpoint"
"CoInductive"
"Fixpoint"
"Inductive"
"Inductive\\s-+Set"
"Inductive\\s-+Prop"
"Inductive\\s-+Type"
"Mutual\\s-+Inductive"
"Record"
"Scheme"
))

(defvar coq-keywords-goal
  '(
"Correctness"
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
;; commands that have to be counted when undoing
(defvar coq-keywords-undoable-commands
  '(
"Focus"
))


(defvar coq-keywords-not-undoable-commands
  '(
"Add\\s-+ML\\s-+Path"
"AddPath"
"Begin\\s-+Silent"
"Cd"
"Check"
"Chapter"
"Class"
"Coercion"
"DelPath"
"End"
"End\\s-+Silent"
"Eval"
"Extraction"
;; moving this to coq-keywords-undoable-commands
;;"Focus"
"Grammar"
"Hints\\s-+Resolve"
"Hints\\s-+Immediate"
"Hints\\s-+Unfold"
"HintRewrite"
"Hint"
"Infix"
"Initialize"
"Implicit\\s-+Arguments\\s-+On"
"Implicit\\s-+Arguments\\s-+Off"
"Load"
"Local\\s-+Coercion"
"Locate\\s-+File"
"Locate\\s-+Library"
"Locate"
"Opaque"
"Print\\s-+Classes"
"Print\\s-+Coercions"
"Print\\s-+Graph"
"Print\\s-+Grammar"
"Print\\s-+HintDb"
"Print\\s-+Hint"
"Print\\s-+LoadPath"
"Print\\s-+ML\\s-+Path"
"Print\\s-+ML\\s-+Modules"
"Print"
"Proof"
"Pwd"
"Require\\s-+Export"
"Require\\s-+Import"
"Require"
"Reset"
"Search"
"SearchIsos"
;; da: testing moving this 
;; "Section"
"Show\\s-+Programs"
"Show\\s-+Proof"
"Show\\s-+Script"
"Show"
"Syntax"
;;Pierre: moving this to coq-keywords-decl
;;"Tactic\\s-+Definition"
"Transparent"
))


(defvar coq-keywords-commands
  (append coq-keywords-not-undoable-commands  coq-keywords-undoable-commands)
  "All commands keyword")



(defvar coq-tactics
  '(
"Absurd"
"Apply"
"Assumption"
"Auto"
"AutoRewrite"
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
"Decompose"
"Dependent\\s-+Inversion_clear"
"Dependent\\s-+Inversion"
"Destruct"
"Discriminate"
"Double"
"EApply"
"EAuto"
"Elim"
"Exact"
"Exists"
"Fix"
"Generalize"
"Hnf"
"Induction"
"Injection"
"Intro[s]?"
"Intuition"
"Inversion_clear"
"Inversion"
"LApply"
"Left"
"Linear"
"Load"
"Omega"
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
"Ring"
"Simplify_eq"
"Simpl"
"Specialize"
"Split"
"Symmetry"
"Tauto"
"Transitivity"
"Trivial"
"Unfold"
))

(defvar coq-keywords
  (append coq-keywords-goal coq-keywords-save coq-keywords-decl
	  coq-keywords-defn coq-keywords-commands)
  "All keywords in a Coq script")

(defvar coq-tacticals 
  '(
    "Abstract"
    "Do"
    "Idtac"
    "Orelse"
    "Repeat"
    "Try")
  "Keywords for tacticals in a Coq script")

(defvar coq-reserved
  '(
    "as"
    "ALL"
    "Cases"
    "EX"
    "else"
    "end"
    "Fix"
    "if"
    "in"
    "let"
    "of"
    "then"
    "using"
    "with"
    )
  "Reserved keyworkds of Coq")

(defvar coq-symbols
  '(
    "|"
    ":"
    ";"
    ","
    "("
    ")"
    "["
    "]"
    "{"
    "}"
    ":="
    "=>"
    "->"
    "."
    )
  "Punctuation Symbols used by Coq")

;; ----- regular expressions
(defvar coq-error-regexp "^\\(Error\\|Discarding\\|Syntax error\\|System Error\\|Anomaly\\)"
  "A regular expression indicating that the Coq process has identified
  an error.")

(defvar coq-id proof-id)

(defvar coq-ids (proof-ids coq-id))

(defun coq-first-abstr-regexp (paren)
  (concat paren "\\s-*\\(" coq-ids "\\)\\s-*:"))

(defun coq-next-abstr-regexp ()
  (concat ";[ \t]*\\(" coq-ids "\\)\\s-*:"))

(defvar coq-font-lock-terms
  (list

   ;; lambda binders
   (list (coq-first-abstr-regexp "\\[") 1 'proof-declaration-name-face)

   ;; Pi binders
   (list (coq-first-abstr-regexp "(") 1 'proof-declaration-name-face)
   
   ;; second, third, etc. abstraction for Lambda of Pi binders
   (list (coq-next-abstr-regexp) 1 'proof-declaration-name-face)

   ;; Kinds
   (cons "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\>" 'font-lock-type-face))

  "*Font-lock table for Coq terms.")

;; According to Coq, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see coq-global-p.
(defconst coq-save-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp coq-keywords-save)))
(defconst coq-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-save)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*\."))
(defconst coq-goal-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp coq-keywords-goal)))
(defconst coq-goal-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-goal)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*[:]?")) 
          ;; Papageno : ce serait plus propre d'omettre le `:' 
          ;; uniquement pour Correctness
          ;; et pour Definition f [x,y:nat] := body
(defconst coq-decl-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-decl)
	  "\\)\\s-+\\(" coq-ids "\\)\\s-*[:]"))
(defconst coq-defn-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-defn)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*[:]"))

(defvar coq-font-lock-keywords-1
   (append
    coq-font-lock-terms
    (list
     (cons (proof-ids-to-regexp coq-keywords) 'font-lock-keyword-face)
     (cons (proof-ids-to-regexp coq-tactics) 'proof-tactics-name-face)
     (cons (proof-ids-to-regexp coq-tacticals) 'proof-tacticals-name-face)
     (cons (proof-ids-to-regexp coq-reserved) 'font-lock-type-face)
     (cons "============================" 'font-lock-keyword-face)
     (cons "Subtree proved!" 'font-lock-keyword-face)
     (cons "subgoal [0-9]+ is:" 'font-lock-keyword-face)
     (list "^\\([^ \n]+\\) \\(is defined\\)" 
	   (list 2 'font-lock-keyword-face t)
	   (list 1 'font-lock-function-name-face t))

     (list coq-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-decl-with-hole-regexp 2 'proof-declaration-name-face)
     (list coq-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-save-with-hole-regexp 2 'font-lock-function-name-face))))

(defun coq-init-syntax-table ()
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
  (modify-syntax-entry ?_  "w")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(provide 'coq-syntax)
