;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997, 1998 LFCS Edinburgh. 
;; Authors: Thomas Kleymann and Healfdene Goguen
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre Courtieu <courtieu@lri.fr>

;; $Id$

(require 'proof-syntax)
(require 'coq-db)

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
      (let* ((str (shell-command-to-string (concat coq-prog-name " -v")))
             ;; this match sets match-string below
             (ver (string-match "version \\([.0-9]*\\)" str)))
        (message str)
        (let ((num (and ver (match-string 1 str))))
          (cond
           ((and num (string-match "\\<8.1" num))
            (message v81)
            (setq coq-version-is-V8-1 t))
           (t;; temporary, should be 8.1 when it is officially out
            (message (concat "Falling back to default: " v80))
            (setq coq-version-is-V8-0 t)))))))))


;;; keyword databases


(defcustom coq-user-tactics-db nil
  "User defined tactic information.  See `coq-syntax-db' for
syntax. It is not necessary to add your own tactics here (it is not
needed by the synchronizing/backtracking system). You may however do
so for the following reasons:

  1 your tactics will be colorized by font-lock

  2 your tactics will be added to the menu and to completion when
  calling \\[coq-insert-tactic]

  3 you may define an abbreviation for your tactic."

  :type '(repeat string)
  :group 'coq)


(defcustom coq-user-commands-db nil
  "User defined command information.  See `coq-syntax-db' for
syntax. It is not necessary to add your own commands here (it is not
needed by the synchronizing/backtracking system). You may however do
so for the following reasons:

  1 your commands will be colorized by font-lock

  2 your commands will be added to the menu and to completion when
  calling \\[coq-insert-command]

  3 you may define an abbreviation for your command."

  :type '(repeat string)
  :group 'coq)


(defvar coq-tactics-db
  '(
    ("absurd " "abs" "absurd " t "absurd")
    ("apply" "ap" "apply " t "apply")
    ("assert by" "assb" "assert ( # : # ) by #" t "assert")
    ("assert" "ass" "assert ( # : # )" t "assert")
    ("assumption" "as" "assumption" t "assumption")
    ("auto with arith" "awa" "auto with arith" t)
    ("auto with" "aw" "auto with @{db}" t)
    ("auto" "a" "auto" t "auto")
    ("autorewrite with in using" "arwiu" "autorewrite with @{db,db...} in @{hyp} using @{tac}" t)
    ("autorewrite with in" "arwi" "autorewrite with @{db,db...} in @{hyp}" t)
    ("autorewrite with using" "arwu" "autorewrite with @{db,db...} using @{tac}" t)
    ("autorewrite with" "ar" "autorewrite with @{db,db...}" t "autorewrite")
    ("cases" "c" "cases " t "cases")
    ("cbv" "cbv" "cbv beta [#] delta iota zeta" t "cbv")
    ("change in" "chi" "change # in #" t)
    ("change with in" "chwi" "change # with # in #" t)
    ("change with" "chw" "change # with" t)
    ("change" "ch" "change " t "change")
    ("clear" "cl" "clear" t "clear")
    ("clearbody" "cl" "clearbody" t "clearbody")
    ("cofix" "cof" "cofix" t "cofix")
    ("coinduction" "coind" "coinduction" t "coinduction")
    ("compare" "cmpa" "compare # #" t "compare")
    ("compute" "cmpu" "compute" t "compute")
    ("congruence" "cong" "congruence" t "congruence")
    ("constructor" "cons" "constructor" t "constructor")
    ("contradiction" "contr" "contradiction" t "contradiction")
    ("cut" "cut" "cut" t "cut")
    ("cutrewrite" "cutr" "cutrewrite -> # = #" t "cutrewrite")
    ("decide equality" "deg" "decide equality" t "decide\\-+equality")
    ("decompose" "dec" "decompose [#] #" t "decompose")
    ("decompose record" "decr" "decompose record #" t "decompose\\s-+record")
    ("decompose sum" "decs" "decompose sum #" t "decompose\\-+sum")
    ("dependent inversion" "depinv" "dependent inversion" t "dependent\\s-+inversion")
    ("dependent inversion with" "depinvw" "dependent inversion # with #" t)
    ("dependent inversion_clear" "depinvc" "dependent inversion_clear" t "dependent\\s-+inversion_clear")
    ("dependent inversion_clear with" "depinvw" "dependent inversion_clear # with #" t)
    ("dependent rewrite ->" "depr" "dependent rewrite -> @{id}" t "dependent\\s-+rewrite")
    ("dependent rewrite <-" "depr<" "dependent rewrite <- @{id}" t)
    ("destruct as" "desa" "destruct # as #" t)
    ("destruct using" "desu" "destruct # using #" t)
    ("destruct" "des" "destruct " t  "destruct")
    ("discriminate" "dis" "discriminate" t "discriminate")
    ("discrR" "discrR" "discrR" t "discrR")
    ("double induction" "dind" "double induction # #" t "double\\s-+induction")
    ("eapply" "eap" "eapply #" t "eapply")
    ("eauto with arith" "eawa" "eauto with arith" t)
    ("eauto with" "eaw" "eauto with @{db}" t)
    ("eauto" "ea" "eauto" t "eauto")
    ("econstructor" "econs" "econstructor" t "econstructor")
    ("eexists" "eex" "eexists" t "eexists")
    ("eleft" "eleft" "eleft" t "eleft")
    ("elim using" "elu" "elim # using #" t)
    ("elim" "e" "elim #" t "elim")
    ("elimtype" "elt" "elimtype" "elimtype")
    ("eright" "erig" "eright" "eright")
    ("esplit" "esp" "esplit" t "esplit")
    ("exact" "exa" "exact" t "exact")
    ("exists" "ex" "exists #" t "exists")
    ("fail" "fa" "fail" nil)
    ("field" "field" "field" t "field")
    ("firstorder" "fsto" "firstorder" t "firstorder")
    ("firstorder with" "fsto" "firstorder with #" t)
    ("firstorder with using" "fsto" "firstorder # with #" t)
    ("fold" "fold" "fold #" t "fold")
    ("fourier" "four" "fourier" t "fourier")
    ("functional induction" "fi" "functional induction @{f} @{args}" t "functional\\s-+induction")
    ("generalize" "g" "generalize #" t "generalize")
    ("generalize dependent" "gd" "generalize dependent #" t "generalize\\s-+dependent")
    ("hnf" "hnf" "hnf" t "hnf")
    ("idtac" "id" "idtac" nil "idtac") ; also in tacticals with abbrev id
    ("idtac \"" "id\"" "idtac \"#\"") ; also in tacticals
    ("induction" "ind" "induction #" t "induction")
    ("induction using" "indu" "induction # using #" t)
    ("injection" "inj" "injection #" t "injection")
    ("instantiate" "inst" "instantiate" t "instantiate")
    ("intro" "i" "intro" t "intro")
    ("intro after" "ia" "intro # after #" t)
    ("intros" "is" "intros #" t "intros")
    ("intros! (guess names)" nil "intros #" nil nil coq-insert-intros)
    ("intros until" "isu" "intros until #" t)
    ("intuition" "intu" "intuition #" t "intuition")
    ("inversion" "inv" "inversion #" t "inversion")
    ("inversion in" "invi" "inversion # in #" t)
    ("inversion using" "invu" "inversion # using #" t)
    ("inversion using in" "invui" "inversion # using # in #" t)
    ("inversion_clear" "invcl" "inversion_clear" t "inversion_clear")
    ("lapply" "lap" "lapply" t "lapply")
    ("lazy" "lazy" "lazy beta [#] delta iota zeta" t "lazy")
    ("left" "left" "left" t "left")
    ("linear" "lin" "linear" t "linear")
    ("load" "load" "load" t "load")
    ("move after" "mov" "move # after #" t "move")
    ("omega" "o" "omega" t "omega")
    ("pattern" "pat" "pattern" t "pattern")
    ("pattern(s)" "pats" "pattern # , #" t)
    ("pattern at" "pata" "pattern # at #" t)
    ("pose" "po" "pose ( # := # )" t "pose")
    ("prolog" "prol" "prolog" t "prolog")
    ("quote" "quote" "quote" t "quote")
    ("quote []" "quote2" "quote # [#]" t)
    ("red" "red" "red" t "red")
    ("refine" "ref" "refine" t "refine")
    ("reflexivity" "refl" "reflexivity #" t "reflexivity")
    ("rename into" "ren" "rename # into #" t "rename")
    ("replace with" "rep" "replace # with #" t)
    ("replace with in" "repi" "replace # with # in #" t)
    ("rewrite <- in" "ri<" "rewrite <- # in #" t)
    ("rewrite <-" "r<" "rewrite <- #" t)
    ("rewrite in" "ri" "rewrite # in #" t)
    ("rewrite" "r" "rewrite #" t "rewrite")
    ("right" "rig" "right" t "right")
    ("ring" "ring" "ring #" t "ring")
    ("set in * |-" "seth" "set ( # := #) in * |-" t)
    ("set in *" "set*" "set ( # := #) in *" t)
    ("set in |- *" "setg" "set ( # := #) in |- *" t)
    ("set in" "seti" "set ( # := #) in #" t)
    ("set" "set" "set ( # := #)" t "set")
    ("setoid_replace with" "strep" "setoid_replace # with #" t "setoid_replace")
    ("simpl" "s" "simpl" t "simpl")
    ("simpl" "sa" "simpl # at #" t)
    ("simple destruct" "sdes" "simple destruct" t "simple\\s-+destruct")
    ("simple inversion" "sinv" "simple inversion" t "simple\\s-+inversion")
    ("simple induction" "sind" "simple induction" t "simple\\s-+induction")
    ("simplify_eq" "simeq" "simplify_eq @{hyp}" t "simplify_eq")
    ("specialize" "spec" "specialize" t "specialize")
    ("split" "sp" "split" t "split")
    ("split_Rabs" "spra" "splitRabs" t "split_Rabs")
    ("split_Rmult" "sprm" "splitRmult" t "split_Rmult")
    ("stepl" "stl" "stepl #" t "stepl")
    ("stepl by" "stlb" "stepl # by #" t)
    ("stepr" "str" "stepr #" t "stepr")
    ("stepr by" "strb" "stepr # by #" t)
    ("subst" "su" "subst #" t "subst")
    ("symmetry" "sy" "symmetry" t "symmetry")
    ("symmetry in" "sy" "symmetry in #" t)
    ("tauto" "ta" "tauto" t "tauto")
    ("transitivity" "trans" "transitivity #" t "transitivity")
    ("trivial" "t" "trivial" t "trivial")
    ("trivial with" "t" "trivial with @{db}" t)
    ("unfold" "u" "unfold #" t "unfold")
    ("unfold(s)" "us" "unfold # , #" t)
    ("unfold in" "unfi" "unfold # in #" t)
    ("unfold at" "unfa" "unfold # at #" t)
    )
  "Coq tactics information list. See `coq-syntax-db' for syntax. "
  )

(defvar coq-tacticals-db
  '(
    ("info" nil "info #" nil "info")
    ("solve" nil "solve [ # | # ]" nil "solve")
    ("first" nil "first [ # | # ]" nil "first")
    ("abstract" nil "abstract @{tac} using @{name}." nil "abstract")
    ("do" nil "do @{num} @{tac}" nil "do")
    ("idtac" nil "idtac") ; also in tactics
;    ("idtac \"" nil "idtac \"#\"") ; also in tactics
    ("fail" "fa" "fail" nil "fail")
;    ("fail \"" "fa\"" "fail" nil) ;
;    ("orelse" nil "orelse #" t "orelse")
    ("repeat" nil "repeat #" nil "repeat")
    ("try" nil "try #" nil "try")
    ("progress" nil "progress #" nil "progress")
    ("|" nil "[ # | # ]" nil)
    ("||" nil "# || #" nil)
    )
  "Coq tacticals information list.  See `coq-syntax-db' for syntax.")



(defvar coq-decl-db
  '(
    ("Axiom" "ax" "Axiom # : #" t "Axiom")
    ("Hint Constructors" "hc" "Hint Constructors # : #." t "Hint\\s-+Constructors")
    ("Hint Extern" "he" "Hint Extern @{cost} @{pat} => @{tac} : @{db}." t "Hint\\s-+Extern")
    ("Hint Immediate" "hi" "Hint Immediate # : @{db}." t "Hint\\s-+Immediate")
    ("Hint Resolve" "hr" "Hint Resolve # : @{db}." t "Hint\\s-+Resolve")
    ("Hint Rewrite ->" "hrw" "Hint Rewrite -> @{t1,t2...} using @{tac} : @{db}." t "Hint\\s-+Rewrite")
    ("Hint Rewrite <-" "hrw" "Hint Rewrite <- @{t1,t2...} using @{tac} : @{db}." t )
    ("Hint Unfold" "hu" "Hint Unfold # : #." t "Hint\\s-+Unfold")
    ("Hypothesis" "hyp" "Hypothesis #: #" t "Hypothesis")
    ("Hypotheses" "hyp" "Hypotheses #: #" t "Hypotheses")
    ("Parameter" "par" "Parameter #: #" t "Parameter")
    ("Parameters" "par" "Parameter #: #" t "Parameters")
    ("Conjecture" "conj" "Conjecture #: #." t "Conjecture")
    ("Variable" "v" "Variable #: #." t "Variable")
    ("Variables" "vs" "Variables # , #: #." t "Variables")	
    ("Coercion" "coerc" "Coercion @{id} : @{typ1} >-> @{typ2}." t "Coercion")
    )
  "Coq declaration keywords information list. See `coq-syntax-db' for syntax."
  )

(defvar coq-defn-db
  '(
    ("CoFixpoint" "cfix" "CoFixpoint # (#:#) : # :=\n#." t "CoFixpoint")
    ("Coinductive" "coindv" "Coinductive # : # :=\n|# : #." t "Coinductive") 
    ("Declare Module : :=" "dm" "Declare Module # : # := #." t "Declare\\s-+Module")
    ("Declare Module <: :=" "dm2" "Declare Module # <: # := #." t);; careful
    ("Definition" "def" "Definition #:# := #." t "Definition");; careful
    ("Definition (2 args)" "def2" "Definition # (# : #) (# : #):# := #." t)
    ("Definition (3 args)" "def3" "Definition # (# : #) (# : #) (# : #):# := #." t)
    ("Definition (4 args)" "def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." t)
    ("Derive Inversion" nil "Derive Inversion @{id} with # Sort #." t "Derive\\s-+Inversion")
    ("Derive Dependent Inversion" nil "Derive Dependent Inversion @{id} with # Sort #." t "Derive\\s-+Dependent\\s-+Inversion")
    ("Derive Inversion_clear" nil "Derive Inversion_clear @{id} with # Sort #." t "Derive\\s-+Inversion")
    ("Fixpoint" "fix" "Fixpoint # (#:#) {struct @{arg}} : # :=\n#." t "Fixpoint")
    ("Function" "func" "Function # (#:#) {struct @{arg}} : # :=\n#." t "Function")
    ("Function measure" "funcm" "Function # (#:#) {measure @{f} @{arg}} : # :=\n#." t)
    ("Function wf" "func wf" "Function # (#:#) {wf @{R} @{arg}} : # :=\n#." t)
    ("Functional Scheme with" "fsw" "Functional Scheme @{name} := Induction for @{fun} with @{mutfuns}." t )
    ("Functional Scheme" "fs" "Functional Scheme @{name} := Induction for @{fun}." t "Functional\\s-+Scheme")
    ("Inductive" "indv" "Inductive # : # := # : #." t "Inductive")
    ("Inductive (2 args)" "indv2" "Inductive # : # :=\n| # : #\n| # : #." t )
    ("Inductive (3 args)" "indv3" "Inductive # : # :=\n| # : #\n| # : #\n| # : #." t )
    ("Inductive (4 args)" "indv4" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #." t )
    ("Inductive (5 args)" "indv5" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #\n| # : #." t )
    ("Let" "Let" "Let # : # := #." t "Let")
    ("Ltac" "ltac" "Ltac # := #" t "Ltac")
    ("Module :=" "mo" "Module # : # := #." t ) ; careful
    ("Module <: :=" "mo2" "Module # <: # := #." t ) ; careful
    ("Record" "rec" "Record # : # := {\n# : #;\n# : # }" t "Record")
    ("Scheme" "sc" "Scheme @{name} := #." t "Scheme")
    ("Scheme Induction" "sci" "Scheme @{name} := Induction for # Sort #." t)
    ("Scheme Minimality" "scm" "Scheme @{name} := Minimality for # Sort #." t)	
    )
  "Coq definition keywords information list. See `coq-syntax-db' for syntax. "
  )

;; modules and section are indented like goal starters
(defvar coq-goal-starters-db
  '(
    ("Add Morphism" "addmor" "Add Morphism @{f} : @{id}" t "Add\\s-+Morphism")
    ("Chapter" "l" "Chapter # : #." t "Chapter")
    ("Declare Module :" "dmi" "Declare Module # : #.\n#\nEnd #." t)
    ("Declare Module <:" "dmi2" "Declare Module # <: #.\n#\nEnd #." t)
    ("Definition" "def" "Definition #:# := #." t "Definition");; careful
    ("Fact" "l" "Fact # : #." t "Fact")
    ("Lemma" "l" "Lemma # : #.\nProof.\n#\nQed." t "Lemma")
    ("Module! (interactive)" nil "Module # : #.\n#\nEnd #." nil nil coq-insert-section-or-module)
    ("Module :" "moi" "Module # : #.\n#\nEnd #." t "Module") ; careful
    ("Module <:" "moi2" "Module # <: #.\n#\nEnd #." t ) ; careful
    ("Module Type" "mti" "Module Type #.\n#\nEnd #." t "Module\\s-+Type") ; careful
    ("Remark" "l" "Remark # : #.\n#\nQed." t "Remark")
    ("Section" "sec" "Section #." t "Section")
    ("Theorem" "l" "Theorem # : #.\n#\nQed." t "Theorem")
    )
  "Coq goal starters keywords information list. See `coq-syntax-db' for syntax. "
  )

(defvar coq-commands-db
  (append 
   '(
     ("Add Abstract Ring" nil "Add Abstract Ring #." t "Add\\s-+Abstract\\s-+Ring")
     ("Add Abstract Semi Ring" nil "Add Abstract Semi Ring #." t "Add\\s-+Abstract\\s-+Semi\\s-+Ring")
     ("Add Field" nil "Add Field #." t "Add\\s-+Field")
     ("Add LoadPath" nil "Add LoadPath #." nil "Add\\s-+LoadPath")
     ("Add ML Path" nil "Add ML Path #." nil "Add\\s-+ML\\s-+Path")
     ("Add Morphism" nil "Add Morphism #." t "Add\\s-+Morphism")
     ("Add Printing" nil "Add Printing #." t "Add\\s-+Printing")
     ("Add Rec LoadPath" nil "Add Rec LoadPath #." nil "Add\\s-+Rec\\s-+LoadPath")
     ("Add Rec ML Path" nil "Add Rec ML Path #." nil "Add\\s-+Rec\\s-+ML\\s-+Path")
     ("Add Ring" nil "Add Ring #." t "Add\\s-+Ring")
     ("Add Semi Ring" nil "Add Semi Ring #." t "Add\\s-+Semi\\s-+Ring")
     ("Add Setoid" nil "Add Setoid #." t "Add\\s-+Setoid")
     ("Arguments Scope" "argsc" "Arguments Scope @{id} [ @{_} ]" t "Arguments\\s-+Scope")
     ("Bind Scope" "bndsc" "Bind Scope @{scope} with @{type}" t "Bind\\s-+Scope")
     ("Canonical Structure" nil "Canonical Structure #." t "Canonical\\s-+Structure")
     ("Cd" nil "Cd #." "Cd")
     ("Check" nil "Check" "Check")
     ("Close Local Scope" "cllsc" "Close Local Scope #" t "Close\\s-+Local\\s-+Scope")
     ("Close Scope" "clsc" "Close Scope #" t "Close\\s-+Scope")
     ("Comments" nil "Comments #." nil "Comments")
     ("Delimit Scope" "delsc" "Delimit Scope @{scope} with @{id}." t "Delimit\\s-+Scope" )
     ("Eval" nil "Eval #." nil "Eval")
     ("Extract Constant" "extrc" "Extract Constant @{id} => \"@{id}\"." nil "Extract\\s-+Constant")
     ("Extract Inlined Constant" "extric" "Extract Inlined Constant @{id} => \"@{id}\"." nil "Extract\\s-+Inlined\\s-+Constant")
     ("Extract Inductive" "extri" "Extract Inductive @{id} => \"@{id}\" [\"@{id}\" \"@{id...}\"]." nil "Extract")
     ("Extraction" "extr" "Extraction @{id}." nil "Extraction")
     ("Extraction (in a file)" "extrf" "Extraction \"@{file}\" @{id}.")
     ("Extraction Inline" nil "Extraction Inline #." t "Extraction\\s-+Inline")
     ("Extraction NoInline" nil "Extraction NoInline #." t "Extraction\\s-+NoInline")
     ("Extraction Language" "extrlang" "Extraction Language #." t "Extraction\\s-+Language")
     ("Extraction Library" "extrl" "Extraction Library @{id}." nil "Extraction\\s-+Library")
     ("Focus" nil "Focus #." nil "Focus")
     ("Identity Coercion" nil "Identity Coercion #." t "Identity\\s-+Coercion")
     ("Implicit Arguments Off" nil "Implicit Arguments Off." t "Implicit\\s-+Arguments\\s-+Off")
     ("Implicit Arguments On" nil "Implicit Arguments On." t "Implicit\\s-+Arguments\\s-+On")
     ("Import" nil "Import #." t "Import")
     ("Infix" "inf" "Infix \"#\" := # (at level #) : @{scope}." t "Infix")
     ("Inspect" nil "Inspect #." nil "Inspect")
     ("Locate" nil "Locate" nil "Locate")
     ("Locate File" nil "Locate File \"#\"." nil "Locate\\s-+File")
     ("Locate Library" nil "Locate Library #." nil "Locate\\s-+Library")
     ("Notation (assoc)" "notas" "Notation \"#\" := # (at level #, # associativity)." t)
     ("Notation (at assoc)" "notassc" "Notation \"#\" := # (at level #, # associativity) : @{scope}." t)
     ("Notation (at at scope)" "notasc" "Notation \"#\" := # (at level #, # at level #) : @{scope}." t)
     ("Notation (at at)" "nota" "Notation \"#\" := # (at level #, # at level #)." t)
     ("Notation (only parsing)" "notsp" "Notation # := # (only parsing)." t)
     ("Notation (simple)" "nots" "Notation # := #." t "Notation")
     ("Notation Local (only parsing)" "notslp" "Notation Local # := # (only parsing)." t)
     ("Notation Local" "notsl" "Notation Local # := #." t "Notation\\s-+Local")
     ("Opaque" nil "Opaque #." nil "Opaque")
     ("Open Local Scope" "oplsc" "Open Local Scope #" t "Open\\s-+Local\\s-+Scope")
     ("Open Scope" "opsc" "Open Scope #" t "Open\\s-+Scope")
     ("Print" "p" "Print #." nil "Print")
     ("Print Hint" nil "Print Hint." nil "Print\\s-+Hint" coq-PrintHint)
     ("Qed" nil "Qed." nil "Qed")
     ("Recursive Extraction" "recextr" "Recursive Extraction @{id}." nil "Recursive\\s-+Extraction")
     ("Recursive Extraction Library" "recextrl" "Recursive Extraction Library @{id}." nil "Recursive\\s-+Extraction\\s-+Library")
     ("Recursive Extraction Module" "recextrm" "Recursive Extraction Module @{id}." nil "Recursive\\s-+Extraction\\s-+Module")
     ("Remove LoadPath" nil "Remove LoadPath" nil "Remove\\s-+LoadPath")
     ("Remove LoadPath" nil "Remove LoadPath" nil "Remove\\s-+LoadPath")
     ("Require" nil "Require #." t "Require")
     ("Require Export" nil "Require Export #." t "Require\\s-+Export")
     ("Reset Extraction Inline" nil "Reset Extraction Inline." t "Reset\\s-+Extraction\\s-+Inline")
     ("Save" nil "Save." t "Save")
     ("Set Extraction AutoInline" nil "Set Extraction AutoInline" t "Extraction\\s-+AutoInline")
     ("Set Extraction Optimize" nil "Set Extraction Optimize" t "Extraction\\s-+Optimize")
     ("Set Implicit Arguments" nil "Set Implicit Arguments" t "Implicit\\s-+Arguments")
     ("Set Printing Synth" nil "Set Printing Synth" t "Printing\\s-+Synth")
     ("Set Printing Wildcard" nil "Set Printing Wildcard" t "Printing\\s-+Wildcard")
     ("Set Printing All" "sprall" "Set Printing All" t "Printing\\s-+All")
     ("Set Hyps Limit" nil "Set Hyps Limit #." nil "Hyps\\s-+Limit")
     ("Set Printing Coercion" nil "Set Printing Coercion" t "Printing\\s-+Coercions?")
     ("Set Printing Coercions" nil "Set Printing Coercions." t)
     ("Set Printing Notations" "sprn" "Set Printing Notations" t "Printing\\s-+Notations")
     ("Set Undo" nil "Set Undo #." nil "Undo")
     ("Show" nil "Show #." nil "Show")
     ("Transparent" nil "Transparent #." nil "Transparent")
     ("Unfocus" nil "Unfocus." nil "Unfocus")
     ("Unset Extraction AutoInline" nil "Unset Extraction AutoInline" t)
     ("Unset Extraction Optimize" nil "Unset Extraction Optimize" t)
     ("Unset Implicit Arguments" nil "Unset Implicit Arguments" t)
     ("Unset Printing Synth" nil "Unset Printing Synth" t)
     ("Unset Printing Wildcard" nil "Unset Printing Wildcard" t)
     ("Unset Hyps Limit" nil "Unset Hyps Limit" nil)
     ("Unset Printing All" "unsprall" "Unset Printing All" nil)
     ("Unset Printing Coercion" nil "Unset Printing Coercion #." t)
     ("Unset Printing Coercions" nil "Unset Printing Coercions." nil)
     ("Unset Printing Notations" "unsprn" "Unset Printing Notations" nil)
     ("Unset Undo" nil "Unset Undo." nil "Unset\\s-+Undo")
;    ("print" "pr" "print #" "print")
     ) 
   coq-decl-db coq-defn-db coq-goal-starters-db)
  "Coq all commands keywords information list. See `coq-syntax-db' for syntax. "      
  )

(defvar coq-terms-db
  '(
    ("fun (1 args)" "f" "fun #:# => #" nil "fun")
    ("fun (2 args)" "f2" "fun (#:#) (#:#) => #")
    ("fun (3 args)" "f3" "fun (#:#) (#:#) (#:#) => #")
    ("fun (4 args)" "f4" "fun (#:#) (#:#) (#:#) (#:#) => #")
    ("forall" "fo" "forall #:#,#" nil "forall")
    ("forall (2 args)" "fo2" "forall (#:#) (#:#), #")
    ("forall (3 args)" "fo3" "forall (#:#) (#:#) (#:#), #")
    ("forall (4 args)" "fo4" "forall (#:#) (#:#) (#:#) (#:#), #")
    ("if" "if" "if # then # else #" nil "if")
    ("let in" "li" "let # := # in #" nil "let")
    ("match! (from type)" nil "" nil "match" coq-insert-match)
    ("match with" "m" "match # with\n| # => #\nend")
    ("match with 2" "m2" "match # with\n| # => #\n| # => #\nend")
    ("match with 3" "m3" "match # with\n| # => #\n| # => #\n| # => #\nend")
    ("match with 4" "m4" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\nend")
    ("match with 5" "m5" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\n| # => #\nend")
    )
  "Coq terms keywords information list. See `coq-syntax-db' for syntax. "
  )







;;; Goals (and module/sections) starters detection


;; ----- keywords for font-lock.

;; FIXME da: this one function breaks the nice configuration of Proof General:
;; would like to have proof-goal-regexp instead.
;; Unfortunately Coq allows "Definition" and friends to perhaps have a goal, 
;; so it appears more difficult than just a proof-goal-regexp setting.
;; Future improvement may simply to be allow a function value for
;; proof-goal-regexp.

;; FIXME Pierre: the right way IMHO here would be to set a span
;; property 'goalcommand when coq prompt says it (if the name of
;; current proof has changed).

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

; This function is used for amalgamating a proof into a single
; goal-save region (proof-goal-command-p used in
; proof-done-advancing-save in generic/proof-script.el) for coq <
; 8.0. It is the test when looking backward the start of the proof.
; It is NOT used for coq > v8.1
; (coq-find-and-forget in coq.el uses state numbers, proof numbers and
; lemma names given in the prompt)

; compatibility with v8.0, will delete it some day
(defun coq-goal-command-str-v80-p (str)
  "See `coq-goal-command-p'."
  (let* ((match (coq-count-match "\\<match\\>" str))
	 (with (coq-count-match "\\<with\\>" str))
	 (letwith (+ (coq-count-match "\\<let\\>" str) (- with match)))
	 (affect (coq-count-match ":=" str)))
		  
    (and (proof-string-match coq-goal-command-regexp str)
	 (not				; 
	  (and 
	   (proof-string-match "\\`\\(Local\\|Definition\\|Lemma\\|Module\\)\\>" str)
	   (not (= letwith affect))))
	 (not (proof-string-match "\\`Declare\\s-+Module\\(\\w\\|\\s-\\|<\\)*:" str))
	 )
    )
  )

; Module and or section openings are detected syntactically. Module
; *openings* are difficult to detect because there can be Module
; ...with X := ... . So we need to count :='s to detect real openings.

; TODO: have opened section/chapter in the prompt too, and get rid of
; syntactical tests everywhere
(defun coq-module-opening-p (str)
  "Decide whether STR is a module or section opening or not. 
Used by `coq-goal-command-p'"
  (let* ((match (coq-count-match "\\<match\\>" str))
	 (with (coq-count-match "\\<with\\>" str))
	 (letwith (+ (coq-count-match "\\<let\\>" str) (- with match)))
	 (affect (coq-count-match ":=" str)))
    (and (proof-string-match "\\`\\(Module\\)\\>" str)
	 (= letwith affect))
    ))

(defun coq-section-command-p (str)
  (proof-string-match "\\`\\(Section\\|Chapter\\)\\>" str))


(defun coq-goal-command-str-v81-p (str)
  "Decide syntactically whether STR is a goal start or not. Use
  `coq-goal-command-p-v81' on a span instead if possible."
  (coq-goal-command-str-v80-p str)
  )

;; This is the function that tests if a SPAN is a goal start. All it
;; has to do is look at the 'goalcmd attribute of the span.
;; It also looks if this is not a module start.

;; TODO: have also attributes 'modulecmd and 'sectioncmd. This needs
;; something in the coq prompt telling the name of all opened modules
;; (like for open goals), and use it to set goalcmd --> no more need
;; to look at Modules and section (actually indentation will still
;; need it)
(defun coq-goal-command-p-v81 (span)
  "see `coq-goal-command-p'"
  (or (span-property span 'goalcmd)
      ;; module and section starts are detected here
      (let ((str (or (span-property span 'cmd) "")))
	(or (coq-section-command-p str)
	    (coq-module-opening-p str))
      )))

;; In coq > 8.1 This is used only for indentation.
(defun coq-goal-command-str-p (str)
  "Decide whether argument is a goal or not.  Use
  `coq-goal-command-p' on a span instead if posible."
 (cond 
  (coq-version-is-V8-1 (coq-goal-command-str-v81-p str))
  (coq-version-is-V8-0 (coq-goal-command-str-v80-p str))
  (t (coq-goal-command-p-str-v80 str)) ;; this is temporary
  ))

;; This is used for backtracking
(defun coq-goal-command-p (span)
  "Decide whether argument is a goal or not."
 (cond 
  (coq-version-is-V8-1 (coq-goal-command-p-v81 span))
  (coq-version-is-V8-0 (coq-goal-command-str-v80-p (span-property span 'cmd)))
  (t (coq-goal-command-str-v80-p (span-property span 'cmd))) ;; this is temporary
  ))

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

;; Following regexps are all state changing
(defvar coq-keywords-state-changing-misc-commands
  (coq-build-regexp-list-from-db coq-commands-db 'filter-state-changing))


(defvar coq-user-keywords-state-changing-commands
  (coq-build-regexp-list-from-db coq-user-commands-db 'filter-state-changing))

(defvar coq-keywords-goal
  (coq-build-regexp-list-from-db coq-goal-starters-db))

(defvar coq-keywords-decl
  (coq-build-regexp-list-from-db coq-decl-db))

(defvar coq-keywords-defn
  (coq-build-regexp-list-from-db coq-defn-db))


(defvar coq-keywords-state-changing-commands
  (append
	coq-keywords-state-changing-misc-commands
	coq-keywords-decl
	coq-keywords-defn
	coq-keywords-goal
	coq-user-keywords-state-changing-commands))


;; 
(defvar coq-keywords-state-preserving-commands
  (coq-build-regexp-list-from-db 
   (append coq-user-commands-db coq-commands-db)
   'filter-state-preserving))


(defvar coq-keywords-commands
  (append coq-keywords-state-changing-commands
	  coq-keywords-state-preserving-commands)
  "All commands keyword.")

(defvar coq-tacticals
  (coq-build-regexp-list-from-db coq-tacticals-db)
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
    "by"
    "beta" "delta" "iota" "zeta" "after" "until" "at"
    "Sort"
    "Time")
  "Reserved keywords of Coq.")


(defvar coq-state-changing-tactics
  (coq-build-regexp-list-from-db 
   (append coq-user-tactics-db coq-tactics-db)
   'filter-state-changing))


(defcustom coq-user-state-preserving-tactics nil
  "List of user defined Coq tactics that do not need to be backtracked;
like \"idtac\" (no other one to my knowledge ?).

For example if myidtac and do_nthing are user defined variants of the
idtac (Nop) tactic, put the following line in your .emacs:

 (setq coq-user-state-preserving-tactics '(\"myidtac\" \"do_nthing\"))"
  :type '(repeat regexp)
  :group 'coq)

(defvar coq-state-preserving-tactics
  (coq-build-regexp-list-from-db 
   (append coq-user-tactics-db coq-tactics-db)
   'filter-state-preserving))


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
    "||"
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
(defvar coq-error-regexp "^\\(Error[:]\\|Discarding pattern\\|Syntax error[:]\\|System Error[:]\\|User Error[:]\\|User error[:]\\|Anomaly[:.]\\|Toplevel input[,]\\)"
  "A regexp indicating that the Coq process has identified an error.")

(defvar coq-id proof-id)
(defvar coq-id-shy "\\(?:\\w\\(?:\\w\\|\\s_\\)*\\)")

(defvar coq-ids (proof-ids coq-id " "))

(defun coq-first-abstr-regexp (paren)
  (concat paren "\\s-*\\(" coq-ids "\\)\\s-*:[^:]")) ; [^: to avoid color on (x::l)]

(defun coq-first-abstr-regexp (paren end)
  (concat paren "\\s-*\\(" coq-ids "\\)\\s-*" end)) 


;; useless now
;(defun coq-next-abstr-regexp ()
;  (concat ";[ \t]*\\(" coq-ids "\\)\\s-*:"))

(defvar coq-font-lock-terms
  (list
   ;; lambda binders
   (list (coq-first-abstr-regexp "fun" "\\(?:=>\\|:\\)") 1 'font-lock-variable-name-face)
   ;; forall binder
   (list (coq-first-abstr-regexp "forall" "\\(?:,\\|:\\)") 1 'font-lock-variable-name-face)
   ;; Pi binders
   (list (coq-first-abstr-regexp "(" ":[^:=]") 1 'font-lock-variable-name-face)
   ;; second, third, etc. abstraction for Lambda of Pi binders
;   (list (coq-next-abstr-regexp) 1 'font-lock-variable-name-face)
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


;;; 'with' is used in tactics too... and ":=" can appear too!! But only
;;; inside parenthesis


;too slow
;(defconst coq-with-with-hole-regexp
;  (concat "\\(" "with"
;          "\\)\\s-+\\(" coq-id "\\)\\s-*"
;	  "\\(?:\\(?:"
;          coq-ids
;          "\\|(" coq-ids ":[^=][^)]*)"
;	  "\\)\\s-*\\)*"
;	  ":" ; : or :=
;	  ))

; faux
;(defconst coq-with-with-hole-regexp
;  (concat "\\(" "with" "\\)\\s-+\\(" coq-id "\\)"))

;faux
;(defconst coq-with-with-hole-regexp
;  (concat "\\(" "with" "\\)\\s-+\\(" coq-ids "\\)" "\\(?:[^:]+\\|:[^=]\\)*:="))

(defconst coq-with-with-hole-regexp
  (concat "\\(with\\)\\s-+\\(" coq-id "\\)\\s-*\\([^(]*:\\|.*)[^(.]*:=\\)")
  ;(concat "\\(" "with" "\\)\\s-+\\(" coq-id "\\)" ".*?)[^(.]*:=")
  )

(defvar coq-font-lock-keywords-1
   (append
    coq-font-lock-terms
    (list
     (cons (proof-ids-to-regexp coq-keywords) 'font-lock-keyword-face)
     (cons (proof-ids-to-regexp coq-tactics ) 'proof-tactics-name-face)
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
     (list coq-with-with-hole-regexp 2 'font-lock-function-name-face)
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

;;; Local Variables: ***
;;; indent-tabs-mode: nil ***
;;; End: ***
