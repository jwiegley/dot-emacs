;; hol-light.el   Basic Proof General instance for HOL Light
;;
;; Copyright (C) 2010-12 LFCS Edinburgh, David Aspinall.
;;
;; Author: David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; $Id$
;;
;; Needs improvement!
;;
;; See the README file in this directory for information.


(require 'proof-easy-config)            ; easy configure mechanism
(require 'proof-syntax)			; functions for making regexps

(defcustom hol-light-home "/home/da/hol_light"
  "*Directory holding the installation of HOL Light."
  :type 'string
  :group 'hol-light)

(defcustom hol-light-startup-cmds 
  (list (concat "#cd \"" hol-light-home "\"") 
	"#use \"hol.ml\"")
  "*Commands used to start up a running HOL Light session."
  :type '(list string)
  :group 'hol-light)



(defvar hol-light-keywords nil)
(defvar hol-light-rules nil)
(defvar hol-light-tactics nil)
(defvar hol-light-tacticals nil)

(proof-easy-config  'hol-light "HOL Light"
 proof-prog-name		 "ocaml"
 proof-terminal-string           ";;"
 proof-script-comment-start      "(*"
 proof-script-comment-end        "*)"
 ;; These are all approximations, of course.
 proof-goal-command-regexp     "^g[ `]"
 proof-save-command-regexp     "pg_top_thm_and_drop"
 proof-goal-with-hole-regexp   "let \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*prove"
 proof-save-with-hole-regexp   "let \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*top_thm()"
 proof-non-undoables-regexp      "b()" ; and others..
 proof-goal-command              "g `%s`;;"
 proof-save-command              "val %s = pg_top_thm_and_drop();;"
 proof-kill-goal-command         "print_string \"Goal killed.\";;" ; nothing to do, repeated goals OK
 proof-showproof-command         "p()"
 proof-undo-n-times-cmd          "(pg_repeat b %s; p());;"
 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "#cd \"%s\";;"
 proof-shell-filename-escapes    '(("\\\\" . "\\\\") ("\""   . "\\\""))
 proof-shell-interrupt-regexp    "Interrupted"
 proof-shell-start-goals-regexp
 (regexp-quote "val it : goalstack = ")
; (proof-regexp-alt "Proof manager status"
;		   "OK.."
;		   "val it =\n")
 proof-shell-end-goals-regexp
 (proof-regexp-alt "^[ \t]*: GoalstackPure.goalstack"
		   "^[ \t]*: GoalstackPure.proofs")
 proof-assistant-home-page           "https://www.cl.cam.ac.uk/~jrh13/hol-light/"
 proof-shell-annotated-prompt-regexp "# "
 proof-shell-error-regexp 
 (proof-regexp-alt "Characters [0-9]+-[0-9]+:" "Exception: Failure")
 proof-shell-init-cmd
 (append hol-light-startup-cmds
	 '("let rec pg_repeat f n = match n with 0 -> () | _ -> (f(); pg_repeat f (n-1))"
	   "let pg_top_thm_and_drop () = let t = top_thm() in ((let _ = b() in ()); t)"))

 ;; FIXME: add optional help topic parameter to help command.
 proof-info-command		    "help \"hol\""
 proof-shell-proof-completed-regexp "Initial goal proved"
 ;; FIXME: next one needs setting so that "urgent" messages are displayed
 ;; eagerly from HOL.
 ;; proof-shell-eager-annotation-start
 proof-find-theorems-command	"DB.match [] (%s);"

 proof-forget-id-command	";" ;; vacuous: but empty string doesn't give
				    ;; new prompt
 ;; We must force this to use ptys since mosml doesn't flush its output
 ;; (on Linux, presumably on Solaris too).
 proof-shell-process-connection-type t

 ;;
 ;; Syntax table entries for proof scripts
 ;;
 proof-script-syntax-table-entries
 '(?\` "\""
   ?\$ "."
   ?\/ "."
   ?\\ "."
   ?+  "."
   ?-  "."
   ?=  "."
   ?%  "."
   ?<  "."
   ?>  "."
   ?\& "."
   ?.  "w"
   ?_  "w"
   ?\' "w"
   ?\| "."
   ?\* ". 23n"
   ?\( "()1"
   ?\) ")(4")

 ;;
 ;; A few of the vast variety of keywords, tactics, tacticals,
 ;; for decorating proof scripts.
 ;;
 ;; In the future, PG will use a mechanism for passing identifier
 ;; lists like this from the proof assistant, we don't really
 ;; want to duplicate all this information here!
 ;;
 hol-light-keywords  '("g" "expand" "e" "let" "store_thm" "top_thm" "by"
		       "Define" "xDefine" "Hol_defn"
		       "Induct" "Cases" "Cases_on" "Induct_on"
		       "std_ss" "arith_ss" "list_ss"
		       "define_type")

 hol-light-rules	 
 '("REFL" "TRANS" "MK_COMB" "ABS" "BETA" "BETA_CONV"
   "ASSUME" "EQ_MP" "DEDUCT_ANTISYM_RULE" "INST_TYPE" "INST"
   "TRUTH" "CONJ" "CONJUNCT1" "CONJUNCT2" "PINST" "PROVE_HYP"
   "T_DEF" "TRUTH" "EQT_ELIM" "EQT_INTRO" "AND_DEF" "CONJ"
   "CONJUNCT1" "CONJUNCT2" "CONJ_PAIR" "CONJUNCTS" "IMP_DEF" "MP"
   "DISCH" "DISCH_ALL" "UNDISCH" "UNDISCH_ALL" "IMP_ANTISYM_RULE" "ADD_ASSUM"
   "EQ_IMP_RULE" "IMP_TRANS" "FORALL_DEF" "SPEC" "SPECL" "SPEC_VAR"
   "SPEC_ALL" "ISPEC" "ISPECL" "GEN" "GENL" "GEN_ALL th"
   "EXISTS_DEF" "EXISTS" "SIMPLE_EXISTS" "CHOOSE" "SIMPLE_CHOOSE" "OR_DEF"
   "DISJ1" "DISJ2" "DISJ_CASES" "SIMPLE_DISJ_CASES" "F_DEF" "NOT_DEF"
   "NOT_ELIM" "NOT_INTRO" "EQF_INTRO" "EQF_ELIM" "CONTR" "EXISTS_UNIQUE_DEF"
   "EXISTENCE"
   "EQ_REFL" "REFL_CLAUSE" "EQ_SYM" "EQ_SYM_EQ" "EQ_TRANS"
   "AC" "BETA_THM" "ABS_SIMP" "CONJ_ASSOC" "CONJ_SYM"
   "CONJ_ACI" "DISJ_ASSOC" "DISJ_SYM" "DISJ_ACI" "IMP_CONJ"
   "IMP_IMP" "IMP_CONJ_ALT" "LEFT_OR_DISTRIB" "RIGHT_OR_DISTRIB" "FORALL_SIMP"
   "EXISTS_SIMP" "EQ_IMP" "EQ_CLAUSES" "NOT_CLAUSES_WEAK" "AND_CLAUSES"
   "OR_CLAUSES" "IMP_CLAUSES" "IMP_EQ_CLAUSE" "EXISTS_UNIQUE_THM" "EXISTS_REFL"
   "EXISTS_UNIQUE_REFL" "UNWIND_THM1" "UNWIND_THM2" "FORALL_UNWIND_THM2" "FORALL_UNWIND_THM1"
   "SWAP_FORALL_THM" "SWAP_EXISTS_THM" "FORALL_AND_THM" "AND_FORALL_THM" "LEFT_AND_FORALL_THM"
   "RIGHT_AND_FORALL_THM" "EXISTS_OR_THM" "OR_EXISTS_THM" "LEFT_OR_EXISTS_THM" "RIGHT_OR_EXISTS_THM"
   "LEFT_EXISTS_AND_THM" "RIGHT_EXISTS_AND_THM" "TRIV_EXISTS_AND_THM" 
   "LEFT_AND_EXISTS_THM" "RIGHT_AND_EXISTS_THM"
   "TRIV_AND_EXISTS_THM" "TRIV_FORALL_OR_THM" 
   "TRIV_OR_FORALL_THM" "RIGHT_IMP_FORALL_THM" "RIGHT_FORALL_IMP_THM"
   "LEFT_IMP_EXISTS_THM" "LEFT_FORALL_IMP_THM" "TRIV_FORALL_IMP_THM" 
   "TRIV_EXISTS_IMP_THM" "EXISTS_UNIQUE_ALT" "EXISTS_UNIQUE")

 hol-light-tactics   
 '("ABS_TAC" "ACCEPT_TAC" "ALL_TAC" "ANTS_TAC" "AP_TERM_TAC"
   "AP_THM_TAC" "ASSUME_TAC" "BETA_TAC" "BINOP_TAC" "CHANGED_TAC"
   "CHEAT_TAC" "CHOOSE_TAC" "CONJ_TAC" "CONTR_TAC" "CONV_TAC"
   "DISCARD_TAC" "DISCH_TAC" "DISJ1_TAC" "DISJ2_TAC" "DISJ_CASES_TAC"
   "EQ_TAC" "EXISTS_TAC" "FAIL_TAC" "GEN_TAC" "LABEL_TAC"
   "MATCH_ACCEPT_TAC" "MATCH_MP_TAC " "META_EXISTS_TAC" "META_SPEC_TAC" "MK_COMB_TAC"
   "MP_TAC" "NO_TAC" "RECALL_ACCEPT_TAC" "REFL_TAC" "REPLICATE_TAC"
   "RULE_ASSUM_TAC " "SPEC_TAC" "STRIP_ASSUME_TAC" "STRIP_GOAL_THEN" "STRIP_TAC"
   "STRUCT_CASES_TAC" "SUBGOAL_TAC" "SUBST1_TAC" "SUBST_ALL_TAC" "SUBST_VAR_TAC"
   "UNDISCH_TAC" "X_CHOOSE_TAC" "X_GEN_TAC" "X_META_EXISTS_TAC")

 hol-light-tacticals 
 '("ORELSE" "FIRST" "CHANGED_TAC" "THEN" "THENL" 
   "EVERY" "REPEAT" "MAP_EVERY"
   "IMP_RES_THEN"
   "FIND_ASSUM" "POP_ASSUM" "ASSUM_LIST" "EVERY_ASSUM" "FIRST_ASSUM"
   "CONJUCTS_THEN" "DISJ_CASES_THEN" "DISCH_THEN" "X_CHOOSE_THEN" "MAP_EVERY"
   "CHOOSE_THEN" "STRIP_THM_THEN" "SUBGOAL_THEN" "FREEZE_THEN")

 proof-script-font-lock-keywords
 (list
  (cons (proof-ids-to-regexp hol-light-keywords) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp hol-light-tactics) 'proof-tactics-name-face)
  (cons (proof-ids-to-regexp hol-light-rules) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp hol-light-tacticals) 'proof-tacticals-name-face))

 ;;
 ;; Some decoration of the goals output [FIXME: not yet HOL Light]
 ;;
 proof-goals-font-lock-keywords
 (list
  (cons (proof-ids-to-regexp '("Proof manager status"
			       "proof" "Incomplete"
			       "Initial goal proved"
			       "Initial goal"
			       "There are currently no proofs"
			       "OK"))
	'font-lock-keyword-face)
  (cons (regexp-quote "------------------------------------")
	'font-lock-comment-face)
  (cons ": GoalstackPure.goalstack" 'proof-boring-face)
  (cons ": GoalstackPure.proofs"    'proof-boring-face)
  (cons ": Thm.thm"		    'proof-boring-face)
  (cons "val it ="		    'proof-boring-face))

 ;;
 ;; Some decoration of the response output
 ;;
 proof-goals-font-lock-keywords
 (setq 
  proof-goals-font-lock-keywords
  (list
   ;; Help system output
   (cons (proof-ids-to-regexp 
	  '("^----------[-]+$"
	    "SYNOPSIS" "DESCRIPTION" "FAILURE CONDITIONS"
	    "EXAMPLES" "SEE ALSO"))
	 'font-lock-keyword-face)
   (cons ": GoalstackPure.goalstack" 'proof-boring-face)
   (cons ": GoalstackPure.proofs"    'proof-boring-face)
   (cons ": Thm.thm"		    'proof-boring-face)
   (cons "val it ="		    'proof-boring-face)))

 ;; End of easy config.
 )


(warn "Hol Light Proof General is incomplete!  Please help improve it!
Read the manual, make improvements, upload at http://proofgeneral.inf.ed.ac.uk/trac")

(provide 'hol-light)
