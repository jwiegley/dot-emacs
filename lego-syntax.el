;; lego-syntax.el Font lock expressions for LEGO
;; Copyright (C) 1994, 1995, 1996, 1997 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequeira
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 2.0  1998/08/11 14:59:58  da
;; New branch
;;
;; Revision 1.2  1998/08/11 11:43:14  da
;; Renamed <file>-fontlock to <file>-syntax
;;
;; Revision 1.6  1998/07/27 15:39:53  tms
;; Supports official LEGO release 1.3
;;
;; Revision 1.5  1998/05/29 09:49:40  tms
;; o outsourced indentation to proof-indent
;; o support indentation of commands
;; o replaced test of Emacs version with availability test of specific
;;   features
;; o C-c C-c, C-c C-v and M-tab is now available in all buffers
;;
;; Revision 1.4  1998/05/22 09:37:12  tms
;; included "Invert" in `lego-keywords'
;;
;; Revision 1.3  1997/11/26 14:11:29  tms
;; simplified code:
;;   lego-goal-with-hole-regexp and lego-save-with-hole-regexp is now
;;   used for lego-font-lock-keywords-1 as well
;;
;; Revision 1.2  1997/10/13 17:13:14  tms
;; *** empty log message ***
;;
;; Revision 1.1.2.2  1997/10/08 08:22:31  hhg
;; Updated undo, fixed bugs, more modularization
;;
;; Revision 1.1.2.1  1997/10/07 13:34:23  hhg
;; New structure to share as much as possible between LEGO and Coq.
;;
;;


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

(defun lego-decl-defn-regexp (char)
    (concat "\\[\\s *\\(" lego-ids
 "\\)\\s *\\(\\[[^]]+\\]\\s *\\)*" char))
; Examples
;              ^        ^^^^        ^^^^^^^^^^^^^^^^^^^^^^^  ^^^^
;              [        sort                                 =
;              [        sort        [n:nat]                  =
;              [        sort        [abbrev=...][n:nat]      =

(defvar lego-font-lock-terms
  (list

   ; lambda binders
     (list (lego-decl-defn-regexp "[:|]") 1
	   'font-lock-declaration-name-face)

     ; let binders
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
