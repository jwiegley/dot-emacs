;; lego-fontlock.el Font lock expressions for LEGO
;; Copyright (C) 1994, 1995, 1996, 1997 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequeira
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

(require 'proof-syntax)

;; ----- keywords for font-lock.

(defconst lego-keywords-goal '("$?Goal"))

(defconst lego-keywords-save '("$?Save" "SaveFrozen" "SaveUnfrozen"))

(defconst lego-commands
  (append lego-keywords-goal lego-keywords-save
	  '("allE" "allI" "andE" "andI" "Assumption" "Claim"
	    "Cut" "Discharge" "DischargeKeep"
	    "echo" "exE" "exI" "Expand" "ExpAll"
	    "ExportState" "Equiv" "For" "Freeze" "Hnf" "Immed"
	    "impE" "impI" "Induction" "Inductive" 
	    "Invert" "Init" "intros" "Intros" "Module" "Next" 
	    "Normal" "notE" "notI" "orE" "orIL" "orIR" "qnify" "Qnify"
	    "Qrepl" "Record" "Refine" "Repeat" "Try" "Unfreeze"))
  "Subset of LEGO keywords and tacticals which are terminated by a \?;")

(defconst lego-keywords
  (append lego-commands
	  '("Constructors" "Double" "ElimOver" "Fields" "Import" "Inversion"
	    "NoReductions" "Parameters" "Relation" "Theorems")))

(defconst lego-tacticals '("Then" "Else" "Try" "Repeat" "For"))

;; ----- regular expressions for font-lock
(defvar lego-error-regexp "^\\(Error\\|Lego parser\\)"
  "A regular expression indicating that the LEGO process has
  identified an error.") 

(defvar lego-id proof-id)

(defvar lego-ids (concat lego-id "\\(\\s *,\\s *" lego-id "\\)*")
  "*For font-lock, we treat \",\" separated identifiers as one identifier
  and refontify commata using \\{lego-fixup-change}.")

(defconst lego-arg-list-regexp "\\s *\\(\\[[^]]+\\]\\s *\\)*"
  "Regular expression maching a list of arguments.")

(defun lego-decl-defn-regexp (char)
    (concat "\\[\\s *\\(" lego-ids "\\)" lego-arg-list-regexp char))
; Examples
;              ^        ^^^^        ^^^^^^^^^^^^^^^^^^^^^^^  ^^^^
;              [        sort                                 =
;              [        sort        [n:nat]                  =
;              [        sort        [abbrev=...][n:nat]      =

(defconst lego-definiendum-alternative-regexp
  (concat "\\(" lego-id "\\)" lego-arg-list-regexp "\\s * ==")
  "Regular expression where the first match identifies the definiendum.")

(defvar lego-font-lock-terms
  (list

   ; lambda binders
     (list (lego-decl-defn-regexp "[:|]") 1
	   'font-lock-declaration-name-face)

     ; let binders
     (list lego-definiendum-alternative-regexp 1 'font-lock-function-name-face)
     (list (lego-decl-defn-regexp "=") 1 'font-lock-function-name-face)

     ; Pi and Sigma binders
     (list (concat "[{<]\\s *\\(" lego-ids "\\)") 1
	   'font-lock-declaration-name-face)
   
     ;; Kinds
     (cons (concat "\\<Prop\\>\\|\\<Type\\s *\\(("
		   lego-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for LEGO terms.")

;; Instead of "[^:]+", it may be better to use "lego-id". Furthermore,
;; it might be safer to append "\\s-*:".
(defconst lego-goal-with-hole-regexp
  (concat "\\(" (ids-to-regexp lego-keywords-goal) "\\)\\s-+\\([^:]+\\)")
  "Regular expression which matches an entry in `lego-keywords-goal'
  and the name of the goal.") 

(defconst lego-save-with-hole-regexp
  (concat "\\(" (ids-to-regexp lego-keywords-save) "\\)\\s-+\\([^;]+\\)")
  "Regular expression which matches an entry in
  `lego-keywords-save' and the name of the goal.")

(defvar lego-font-lock-keywords-1
   (append
    lego-font-lock-terms
    (list
     (cons (ids-to-regexp lego-keywords) 'font-lock-keyword-face)
     (cons (ids-to-regexp lego-tacticals) 'font-lock-tacticals-name-face)
     (list lego-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list lego-save-with-hole-regexp 2 'font-lock-function-name-face))))
     
(provide 'lego-syntax)
