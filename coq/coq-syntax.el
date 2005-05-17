;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Authors: Thomas Kleymann and Healfdene Goguen
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>

;; $Id$

(require 'proof-syntax)

;; da 15/2/03: without defvars compilation breaks
;; This may have broken some of logic below

;; Pierre: we will have both versions V8.0 and V8.1 during a while the
;; test with "coqtop -v" can be skipped if one of the variables
;; coq-version-is-V8-0/1 is already set (useful for people dealing
;; with several version of coq).

; this one is temporary, for compatibility
(defvar coq-version-is-V8 nil "Obsolete, use `coq-version-is-V8-0' instead.")

(defvar coq-version-is-V8-0 nil 
"This variable can be set to t to force ProofGeneral to coq version
coq-8.0. To do that, put (setq coq-version-is-V8-0 t) in your .emacs and
restart emacs. This variable cannot be true simultaneously with
coq-version-is-V8-1. If none of these 2 variables is set to t, then
ProofGeneral guesses the version of coq by doing 'coqtop -v'." )

(defvar coq-version-is-V8-1 nil 
  "This variable can be set to t to force ProofGeneral to coq version
coq-8.1 (use it for coq-8.0cvs after january 2005). To do that, put
\(setq coq-version-is-V8-1 t) in your .emacs and restart emacs. This
variable cannot be true simultaneously with coq-version-is-V8-0. If
none of these 2 variables is set to t, then ProofGeneral guesses the
version of coq by doing 'coqtop -v'." )

;;FIXME: how to make compilable?
(unless (noninteractive);; DA: evaluating here gives error during compile
  (let* 
		(
		 (seedoc (concat " (to force another version, see for example"
							  " C-h v `coq-version-is-V8-0)'."))
		 (v80 (concat "proofgeneral is in coq 8.0 mode" seedoc))
		 (v81 (concat "proofgeneral is in coq 8.1 mode" seedoc))
		 (err (concat "Both config variables coq-version-is-V8-1 and"
						  " coq-version-is-V8-0 are set to true. This is"
						  "contradictory.")))
	 
	 (cond
	  ((and coq-version-is-V8-1 coq-version-is-V8-0) 
		(error err))
	  (coq-version-is-V8-1 (message v81))
	  (coq-version-is-V8-0 (message v80))
	  (coq-version-is-V8 (setq coq-version-is-V8-0 t coq-version-is-V8-1 nil)
								(message v80))
	  (t;; otherwise do coqtop -v and see which version we have
		(let ((str (shell-command-to-string (concat coq-prog-name " -v"))))
		  ;; this match sets match-string below
		  (string-match "version \\([.0-9]*\\)" str)
		  (message str)
		  (let ((num (match-string 1 str)))
			 ;; da: added this to avoid type error in case coq command fails
			 (if (null num) (setq num ""))
			 (cond
			  ((or (string-match "\\<8.1" num)) 
				(message v81)
				(setq coq-version-is-V8-1 t))			
			  (t ;; temporary, should be 8.1 when it is officially out
				(message (concat "Falling back to default: " v80))
				(setq coq-version-is-V8-0 t)
				))))))))

;; ----- keywords for font-lock.


(defvar coq-keywords-decl
  '("Axiom[s]?"
    "Hypotheses"
    "Hypothesis"
    "Parameter[s]?"
    "Variable[s]?"
    "Global\\s-+Variable"
    ;;added tactic def here because it needs Reset to be undone correctly
    "Tactic\\s-+Definition"
    "Meta\\s-+Definition"
    "Recursive\\s-+Tactic\\s-+Definition"
    "Recursive\\s-+Meta\\s-+Definition"))



(defvar coq-keywords-defn
  '("CoFixpoint"
    "CoInductive"
	 "Definition" ;; careful: if not followed by :=, then it is a goal cmd
    "Fixpoint"
    "CoInductive"
    "Inductive"
    "Inductive\\s-+Set"
    "Inductive\\s-+Prop"
    "Inductive\\s-+Type"
    "Mutual\\s-+Inductive"
    "Record"
    "Scheme"
    "Functional\\s-+Scheme"
    "Syntactic\\s-+Definition"
    "Structure"
	 "Ltac"))

;; Modules are like sections
(defvar coq-keywords-goal
  '("Add\\s-+Morphism"
	 "Chapter"
	 "Declare\\s-+Module";;only if not followed by:=(see coq-proof-mode-p in coq.el)
	 "Module"
	 "Module\\s-+Type"
	 "Section"
	 "Correctness"
	 "Definition";; only if not followed by := (see coq-proof-mode-p in coq.el)
	 "Fact"
	 "Goal"
	 "Lemma"
	 "Local"
	 "Remark"
	 "Theorem"))

;; FIXME da: this one function breaks the nice configuration of Proof General:
;; would like to have proof-goal-regexp instead.
;; Unfortunately Coq allows "Definition" and friends to perhaps have a goal, 
;; so it appears more difficult than just a proof-goal-regexp setting.
;; Future improvement may simply to be allow a function value for
;; proof-goal-regexp.

;; excerpt of Jacek Chrzaszcz, implementer of the module system: sorry
;; for the french:
;*) suivant les suggestions de Chritine, pas de mode preuve dans un type de
;    module (donc pas de Definition truc:machin.  Lemma, Theorem ... )
;
; *) la commande Module M [ ( : | <: ) MTYP ] [ := MEXPR ] est valable
;    uniquement hors d'un MT
;    - si :=MEXPR est absent, elle demarre un nouveau module interactif
;    - si :=MEXPR est present, elle definit un module
;    (la fonction vernac_define_module dans toplevel/vernacentries) 
;
; *) la nouvelle commande Declare Module M [ ( : | <: ) MTYP ] [ := MEXPR ]
;    est valable uniquement dans un MT
;    - si :=MEXPR absent, :MTYP absent, elle demarre un nouveau module
;      interactif
;    - si (:=MEXPR absent, :MTYP present) 
;      ou (:=MEXPR present, :MTYP absent)
;      elle declare un module.
;    (la fonction vernac_declare_module dans toplevel/vernacentries)

(defun coq-count-match (regexp strg)
  "Count the number of (maximum, non overlapping) matching substring 
of STRG matching REGEXP. Empty match are counted once."
  (let ((nbmatch 0) (str strg))
    (while (and (proof-string-match regexp str) (not (string-equal str "")))
      (incf nbmatch)
      (if (= (match-end 0) 0) (setq str (substring str 1))
        (setq str (substring str (match-end 0)))))
    nbmatch))



(defun coq-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (let* ((match (coq-count-match "\\<match\\>" str))
		  (with (coq-count-match "\\<with\\>" str))
		  (letwith (+ (coq-count-match "\\<let\\>" str) (- with match)))
		  (affect (coq-count-match ":=" str)))
		  
	 (and (proof-string-match coq-goal-command-regexp str)
			(not									 ; 
			 (and 
			  (proof-string-match "\\`\\(Local\\|Definition\\|Lemma\\|Module\\)\\>" str)
			  (not (= letwith affect))))
			(not (proof-string-match "\\`Declare\\s-+Module\\(\\w\\|\\s-\\|<\\)*:" str))
			)
	 )
  )


(defvar coq-keywords-save-strict
  '("Defined"
    "Save"
    "Qed"
    "End"
	 "Admitted"
	 ))

(defvar coq-keywords-save
  (append coq-keywords-save-strict '("Proof"))
)

(defun coq-save-command-p (span str)
  "Decide whether argument is a Save command or not"
  (or (proof-string-match coq-save-command-regexp-strict str)
		(and (proof-string-match "\\`Proof\\>" str)
			  (not (proof-string-match "Proof\\s-*\\(\\.\\|\\<with\\>\\)" str)))
		)
  )

(defvar coq-keywords-kill-goal 
  '("Abort"))




(defcustom coq-user-state-changing-commands nil
  "List of user-defined Coq commands that need to be backtracked;
like Require, Definition, etc...

For example if MyHint and MyRequire are user defined variants of the
Hint and Require commands, put the following line in your .emacs:

 (setq coq-user-state-changing-commands '(\"MyHint\" \"MyRequire\"))"
  :type '(repeat regexp)
  :group 'coq)
 

(defcustom coq-user-state-preserving-commands nil
  "List of user defined Coq commands that do not need to be backtracked;
like Print, Check, Show etc...

For example if MyPrint and MyCheck are user defined variants of the
Print and Check commands, put the following line in your .emacs:

 (setq coq-user-state-preserving-commands '(\"MyPrint\" \"MyCheck\"))"
  :type '(repeat regexp)
  :group 'coq)

;; 
;; Print Hint ==> state preserving
(defvar coq-keywords-state-preserving-commands
  (append '("(\\*" ;;Pierre comments must not be undone
	    "Add\\s-+LoadPath"
	    "Add\\s-+ML\\s-+Path"
	    "Add\\s-+Rec\\s-+ML\\s-+Path"
	    "Add\\s-+Rec\\s-+LoadPath"
	    "Cd"
	    "Check"
		 "Comments"
	    "DelPath"
	    "Eval"
	    "Extraction"
	    "Extraction Library"
	    "Extraction Module"
	    "Focus" ;; ???
	    "Inspect"
	    "Locate"
	    "Locate\\s-+File"
	    "Locate\\s-+Library"
	    "Opaque"
	    "Print"
	    "Proof"
	    "Recursive\\s-+Extraction\\(?:\\s-+Module\\)?"
	    "Remove\\s-+LoadPath"
	    "Pwd"
	    "Qed"
	    "Reset"
	    "Save"
	    "Search"
	    "SearchIsos"
	    "SearchPattern"
	    "SearchRewrite"
	    "Set\\s-+Hyps_limit"
	    "Set\\s-+Undo"
	    "Set\\s-+Printing\\s-+Coercion[^s]"
	    "Show"
	    "Test\\s-+Printing\\s-+If"
	    "Test\\s-+Printing\\s-+Let"
	    "Test\\s-+Printing\\s-+Synth"
	    "Test\\s-+Printing\\s-+Wildcard"
	    "Unfocus" ; ???
	    "Unset\\s-+Hyps_limit"
	    "Unset\\s-+Undo"
	    "Unset\\s-+Printing\\s-+Coercion[^s]"
	    "Transparent"
	    "Write\\s-+State")
	  coq-user-state-preserving-commands))

(defvar coq-keywords-state-changing-misc-commands
  '("Add\\s-+Abstract\\s-+Ring"
    "Add\\s-+Abstract\\s-+Semi\\s-+Ring"
    "Add\\s-+Field"
    "Add\\s-+Morphism"
    "Add\\s-+Printing"
    "Add\\s-+Ring"
    "Add\\s-+Semi\\s-+Ring"
    "Add\\s-+Setoid"
    "Begin\\s-+Silent"
    "Canonical\\s-+Structure"
    "CoFixpoint"
    "CoInductive"
    "Coercion"
    "Declare\\s-+ML\\s-+Module"
    "End\\s-+Silent"
    "Derive\\s-+Dependent\\s-+Inversion"
    "Derive\\s-+Dependent\\s-+Inversion_clear"
    "Derive\\s-+Inversion"
    "Derive\\s-+Inversion_clear"
    "Extract\\s-+Constant"
    "Extract\\s-+Inductive"
    "Extraction\\s-+Inline"
    "Extraction\\s-+Language"
    "Extraction\\s-+NoInline"
    "Grammar"
;    "\\`Hint" ;; Pierre fev-2003: Hack: must not match "Print Hint."
	 "Hint\\s-+Resolve"
	 "Hint\\s-+Immediate"
	 "Hint\\s-+Rewrite"
	 "Hint\\s-+Unfold"
	 "Hint\\s-+Extern"
	 "Hint\\s-+Constructors"
    "Identity\\s-+Coercion"
    "Implicit\\s-+Arguments\\s-+Off"
    "Implicit\\s-+Arguments\\s-+On"
    "Implicits"
    "Import"
    "Infix"
    "Load"
	 "Notation"
    "Read\\s-+Module"
    "Remove\\s-+LoadPath"
    "Remove\\s-+Printing\\s-+If\\s-+ident"
    "Remove\\s-+Printing\\s-+Let\\s-+ident"
    "Require"
    "Require\\s-+Export"
    "Reset\\s-+Extraction\\s-+Inline"
    "Reset\\s-+Initial"
    "Restart"
    "Restore\\s-+State"
    "Remove\\s-+Printing\\s-+If\\s-+ident"
    "Remove\\s-+Printing\\s-+Let\\s-+ident"
    "Restore\\s-+State"
    "Set\\s-+Extraction\\s-+AutoInline"
    "Set\\s-+Extraction\\s-+Optimize"
    "Set\\s-+Implicit\\s-+Arguments"
    "Set\\s-+Printing\\s-+Coercions"
    "Set\\s-+Printing\\s-+Synth"
    "Set\\s-+Printing\\s-+Wildcard"
    "Unset\\s-+Extraction\\s-+AutoInline"
    "Unset\\s-+Extraction\\s-+Optimize"
    "Unset\\s-+Implicit\\s-+Arguments"
    "Unset\\s-+Printing\\s-+Coercions"
    "Unset\\s-+Printing\\s-+Synth"
    "Unset\\s-+Printing\\s-+Wildcard"
    "Syntax"
	 "Tactic Notation"
    "Transparent"))




(defvar coq-keywords-state-changing-commands
  (append
	coq-keywords-state-changing-misc-commands
	coq-keywords-decl
	coq-keywords-defn
	coq-keywords-goal
	coq-user-state-changing-commands
	)
  )

(defvar coq-keywords-commands
  (append coq-keywords-state-changing-commands
			 coq-keywords-state-preserving-commands)
  "All commands keyword.")

(defvar coq-tacticals
  '("abstract"
	 "do"
	 "idtac" ;; also in state-preserving-tactic
	 "fail"
	 "orelse"
	 "repeat"
	 "try"
	 "Time")
  "Keywords for tacticals in a Coq script.")

; From JF Monin:
(defvar coq-reserved
  '("False"
	 "True"
	 "after"
	 "as"
	 "cofix"
	 "fix"
	 "forall"
	 "fun"
	 "match"
	 "return"
	 "struct"
    "else"
    "end"
    "if"
    "in"
    "into"
    "let"
    "then"
    "using"
    "with"
	 )
  "Reserved keywords of Coq.")


(defcustom coq-user-state-changing-tactics nil
  "List of user defined Coq tactics that need to be backtracked;
like almost all tactics, but \"Idtac\" (\"Proof\" is a command actually).

For example if MyIntro and MyElim are user defined variants of the
Intro and Elim tactics, put the following line in your .emacs:

 (setq coq-user-state-changing-tactics '(\"MyIntro\" \"MyElim\"))"
  :type '(repeat regexp)
  :group 'coq)

(defvar coq-state-changing-tactics
  (append  
	'(
	  "absurd"
	  "apply"
	  "assert"
	  "assumption"
	  "auto"
	  "autorewrite"
	  "case"
	  "cbv"
	  "change"
	  "clear"
	  "clearbody"
	  "cofix"
	  "compare"
	  "compute"
	  "congruence"
	  "constructor"
	  "contradiction"
	  "cut"
	  "cutrewrite"
	  ;;"dhyp"
	  ;;"dind"
	  "decide equality"
	  "decompose"
	  "dependent inversion"
	  "dependent inversion_clear"
	  "dependent rewrite ->"
	  "dependent rewrite <-"
	  "dependent\\s-+inversion"
	  "dependent\\s-+inversion_clear"
	  "destruct"
	  "discrr"
	  "discriminate"
	  "double\\s-+induction"
	  "eapply"
	  "eauto"
	  "econstructor"
	  "eleft"
	  "eright"
	  "esplit"
	  "eexists"
	  "elim"
	  "elimtype"
	  "exact"
	  "exists"
	  "field"
	  "firstorder"
	  "fix"
	  "fold"
	  "fourier"
	  "generalize"
	  "hnf"
	  "induction"
	  "coinduction"
	  "injection"
	  "instantiate"
	  "intro[s]?"
	  "intuition"
	  "inversion"
	  "inversion_clear"
	  "jp"
	  "lapply"
	  "lazy"
	  "left"
	  "lettac"
	  "linear"
	  "load"
	  "move"
	  "newdestruct"
	  "newinduction"
	  "omega "
	  "pattern"
	  "pose"
	  "program"
	  "program_all"
	  "prolog"
	  "quote"
	  "realizer"
	  "red"
	  "refine"
	  "reflexivity"
	  "rename"
	  "replace"
	  "resume"
	  "rewrite"
	  "right"
	  "ring"
	  "set"
	  "setoid_replace"
	  "simpl"
	  "simple\\s-+inversion"
	  "simplify_eq"
	  "specialize"
	  "split"
	  "splitabsolu"
	  "splitrmult"
	  "suspend"
	  "subst"
	  "symmetry"
	  "tauto"
	  "transitivity"
	  "trivial"
	  "unfold"
	  "functional\\s-+induction")
	coq-user-state-changing-tactics))

(defcustom coq-user-state-preserving-tactics nil
  "List of user defined Coq tactics that do not need to be backtracked;
like \"Idtac\" (no other one to my knowledge ?).

For example if MyIdtac and Do_nthing are user defined variants of the
Idtac (Nop) tactic, put the following line in your .emacs:

 (setq coq-user-state-preserving-tactics '(\"MyIdtac\" \"Do_nthing\"))"
  :type '(repeat regexp)
  :group 'coq)

(defvar coq-state-preserving-tactics
  (append '("Idtac")
	  coq-user-state-preserving-tactics))

(defvar coq-tactics
  (append coq-state-changing-tactics coq-state-preserving-tactics))

(defvar coq-retractable-instruct
  (append coq-state-changing-tactics coq-keywords-state-changing-commands))

(defvar coq-non-retractable-instruct
  (append coq-state-preserving-tactics
			 coq-keywords-state-preserving-commands))

(defvar coq-keywords
  (append coq-keywords-goal coq-keywords-save coq-keywords-decl
	  coq-keywords-defn coq-keywords-commands)
  "All keywords in a Coq script.")



(defvar coq-symbols
  '("|"
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
    ".")
  "Punctuation Symbols used by Coq.")

;; ----- regular expressions
(defvar coq-error-regexp "^\\(Error\\|Discarding\\|Syntax error\\|System Error\\|User Error\\|User error\\|Anomaly\\|Uncaught exception\\|Toplevel input\\)"
  "A regexp indicating that the Coq process has identified an error.")

(defvar coq-id proof-id)
(defvar coq-id-shy "\\(?:\\w\\(?:\\w\\|\\s_\\)*\\)")

(defvar coq-ids (proof-ids coq-id))

(defun coq-first-abstr-regexp (paren)
  (concat paren "\\s-*\\(" coq-ids "\\)\\s-*:"))

(defun coq-next-abstr-regexp ()
  (concat ";[ \t]*\\(" coq-ids "\\)\\s-*:"))

(defvar coq-font-lock-terms
  (list
   ;; lambda binders
   (list (coq-first-abstr-regexp "\\[") 1 'font-lock-variable-name-face)
   ;; Pi binders
   (list (coq-first-abstr-regexp "(") 1 'font-lock-variable-name-face)
   ;; second, third, etc. abstraction for Lambda of Pi binders
   (list (coq-next-abstr-regexp) 1 'font-lock-variable-name-face)
   ;; Kinds
   (cons "\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\>" 'font-lock-type-face))
  "*Font-lock table for Coq terms.")

;; According to Coq, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see coq-global-p.
(defconst coq-save-command-regexp-strict
  (proof-anchor-regexp (proof-ids-to-regexp coq-keywords-save-strict)))
(defconst coq-save-command-regexp
  (proof-anchor-regexp (proof-ids-to-regexp coq-keywords-save)))
(defconst coq-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp coq-keywords-save-strict)
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
          "\\)\\s-+\\(" coq-id "\\)\\s-*\\S-"))
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
     (list coq-decl-with-hole-regexp 2 'font-lock-variable-name-face)
     (list coq-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (list coq-save-with-hole-regexp 2 'font-lock-function-name-face)
     ;; Remove spurious variable and function faces on commas.
     '(proof-zap-commas))))
(defvar coq-font-lock-keywords coq-font-lock-keywords-1)

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
  (modify-syntax-entry ?\' "w")
  (modify-syntax-entry ?\| ".")

; should maybe be "_" but it makes coq-find-and-forget (in coq.el) bug
  (modify-syntax-entry ?\. ".") 

  (condition-case nil
      ;; Try to use Emacs-21's nested comments.
      (modify-syntax-entry ?\* ". 23n")
    ;; Revert to non-nested comments if that failed.
    (error (modify-syntax-entry ?\* ". 23")))
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))


(defconst coq-generic-expression
  (mapcar (lambda (kw) 
	    (list (capitalize kw)
		  (concat "\\<" kw "\\>" "\\s-+\\(\\w+\\)\\W" )
		  1))
	  (append coq-keywords-decl coq-keywords-defn coq-keywords-goal)))


(provide 'coq-syntax)
;;; coq-syntax.el ends here
