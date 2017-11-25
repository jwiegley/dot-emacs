;; coq-syntax.el Font lock expressions for Coq
;; Copyright (C) 1997-2007, 2009 LFCS Edinburgh.
;; Authors: Thomas Kleymann, Healfdene Goguen, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; coq-syntax.el,v 11.13 2013/07/10 14:59:08 pier Exp

(require 'proof-syntax)
(require 'proof-utils)                  ; proof-locate-executable
(require 'coq-db)
(require 'span)

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

  :type '(repeat sexp)
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

  :type '(repeat sexp)
  :group 'coq)

(defcustom coq-user-tacticals-db nil
  "User defined tactical information.  See `coq-syntax-db' for
 syntax. It is not necessary to add your own commands here (it is not
 needed by the synchronizing/backtracking system). You may however do
 so for the following reasons:

   1 your commands will be colorized by font-lock

   2 your commands will be added to the menu and to completion when
   calling \\[coq-insert-command]

   3 you may define an abbreviation for your command."

  :type '(repeat sexp)
  :group 'coq)

(defcustom coq-user-solve-tactics-db nil
  "User defined closing tactics. See `coq-syntax-db' for
 syntax. It is not necessary to add your own commands here (it is not
 needed by the synchronizing/backtracking system). You may however do
 so for the following reasons:

   1 your commands will be colorized by font-lock

   2 your commands will be added to the menu and to completion when
   calling \\[coq-insert-command]

   3 you may define an abbreviation for your command."

  :type '(repeat sexp)
  :group 'coq)

(defcustom coq-user-cheat-tactics-db nil
  "User defined closing tactics BY CHEATING (ex: admit).
 See `coq-syntax-db' for syntax. It is not necessary to add your
 own commands here (it is not needed by the
 synchronizing/backtracking system). You may however do so for
 the following reasons:

   1 your commands will be colorized by font-lock

   2 your commands will be added to the menu and to completion when
   calling \\[coq-insert-command]

   3 you may define an abbreviation for your command."

  :type '(repeat sexp)
  :group 'coq)



(defcustom coq-user-reserved-db nil
  "User defined reserved keywords information.  See `coq-syntax-db' for
 syntax. It is not necessary to add your own commands here (it is not
 needed by the synchronizing/backtracking system). You may however do
 so for the following reasons:

   1 your commands will be colorized by font-lock

   2 your commands will be added to the menu and to completion when
   calling \\[coq-insert-command]

   3 you may define an abbreviation for your command."

  :type '(repeat sexp)
  :group 'coq)


;; user shortcuts are prioritized by being put at the end
(defvar coq-tactics-db
  (append
   '(
     ("absurd " "abs" "absurd " t "absurd")
     ("apply" "ap" "apply " t "apply")
     ("assert by" "assb" "assert ( # : # ) by #" t "assert")
     ("assert" "ass" "assert ( # : # )" t)
     ;;     ("assumption" "as" "assumption" t "assumption")
     ("auto with arith" "awa" "auto with arith" t)
     ("auto with" "aw" "auto with @{db}" t)
     ("auto" "a" "auto" t "auto")
     ("autorewrite with in using" "arwiu" "autorewrite with @{db,db...} in @{hyp} using @{tac}" t)
     ("autorewrite with in" "arwi" "autorewrite with @{db,db...} in @{hyp}" t)
     ("autorewrite with using" "arwu" "autorewrite with @{db,db...} using @{tac}" t)
     ("autorewrite with" "ar" "autorewrite with @{db,db...}" t "autorewrite")
     ("case" nil "case " t "case")
     ("case_eq" "ceq" "case_eq " t "case_eq")
     ("case_type" "cty" "case_type " t "case_type")
     ("cbn" "c" "cbn" t "cbn")
     ("cbn (with flags)" "cbn" "cbn beta delta [#] iota zeta" t "cbn")
     ("cbv" "cbv" "cbv beta delta [#] iota zeta" t "cbv")
     ("change in" "chi" "change # in #" t)
     ("change with in" "chwi" "change # with # in #" t)
     ("change with" "chw" "change # with" t)
     ("change" "ch" "change " t "change")
     ("clear" "cl" "clear" t "clear")
     ("clear dependent" "cldep" "clear dependent" t "clear\\s-+dependent")
     ("clearbody" "cl" "clearbody" t "clearbody")
     ("cofix" "cof" "cofix" t "cofix")
     ("coinduction" "coind" "coinduction" t "coinduction")
     ("compare" "cmpa" "compare # #" t "compare")
     ("compute" "cmpu" "compute" t "compute")
     ;;     ("congruence" "cong" "congruence" t "congruence")
     ("constructor" "cons" "constructor" t "constructor")
     ;;     ("contradiction" "contr" "contradiction" t "contradiction")
     ("cut" "cut" "cut" t "cut")
     ("cutrewrite" "cutr" "cutrewrite -> # = #" t "cutrewrite")
     ;;     ("decide equality" "deg" "decide equality" t "decide\\s-+equality")
     ("decide_right" "decr" "decide_right" t "decide\\s-+right")
     ("decide_left" "decl" "decide_left" t "decide\\s-+left")
     ("decide" nil "decide" t "decide")
     ("decompose record" "decr" "decompose record #" t "decompose\\s-+record")
     ("decompose sum" "decs" "decompose sum #" t "decompose\\s-+sum")
     ("decompose" "dec" "decompose [#] #" t "decompose")
     ("dependent inversion" "depinv" "dependent inversion" t "dependent\\s-+inversion")
     ("dependent inversion with" "depinvw" "dependent inversion # with #" t)
     ("dependent inversion_clear" "depinvc" "dependent inversion_clear" t "dependent\\s-+inversion_clear")
     ("dependent inversion_clear with" "depinvw" "dependent inversion_clear # with #" t)
     ("dependent rewrite ->" "depr" "dependent rewrite -> @{id}" t "dependent\\s-+rewrite")
     ("dependent rewrite <-" "depr<" "dependent rewrite <- @{id}" t)
     ("destr_eq" "deseq" "destr_eq " t  "destr_eq")
     ("destruct as" "desa" "destruct # as #" t)
     ("destruct using" "desu" "destruct # using #" t)
     ("destruct" "des" "destruct " t  "destruct")
     ("destruct_with_eqn" "deswe" "destruct_with_eqn " t  "destruct_with_eqn")
     ("destruct_all" "desall" "destruct_all " t  "destruct_all")
     ;;     ("discriminate" "dis" "discriminate" t "discriminate")
     ("discrR" "discrR" "discrR" t "discrR")
     ("double induction" "dind" "double induction # #" t "double\\s-+induction")
     ("eapply" "eap" "eapply #" t "eapply")
     ("eauto with arith" "eawa" "eauto with arith" t)
     ("eauto with" "eaw" "eauto with @{db}" t)
     ("eauto" "ea" "eauto" t "eauto")
     ("econstructor" "econs" "econstructor" t "econstructor")
     ("edestruct" "edes" "edestruct " t  "edestruct")
     ("eexists" "eex" "eexists" t "eexists")
     ("eleft" "eleft" "eleft" t "eleft")
     ("elim using" "elu" "elim # using #" t)
     ("elim" "e" "elim #" t "elim")
     ("elimtype" "elt" "elimtype" t "elimtype")
     ("enough" "eng" "enough (#: #).\n{ #\n}" t "enough")
     ("erewrite" "er" "erewrite #" t "erewrite")
     ("eright" "erig" "eright" "eright")
     ("esplit" "esp" "esplit" t "esplit")
     ;;     ("exact" "exa" "exact" t "exact")
     ("exfalso" "exf" "exfalso" t "exfalso")
     ("exists" "ex" "exists #" t "exists")
     ;;     ("fail" "fa" "fail" nil)
     ;;     ("field" "field" "field" t "field")
     ("false_hyp" nil "false_hyp @{H} @{G}" t "false_hyp")
     ("firstorder" "fsto" "firstorder" t "firstorder")
     ("firstorder with" "fsto" "firstorder with #" t)
     ("firstorder with using" "fsto" "firstorder # with #" t)
     ("fold" "fold" "fold #" t "fold")
     ;;     ("fourier" "four" "fourier" t "fourier")
     ("functional induction" "fi" "functional induction @{f} @{args}" t "functional\\s-+induction")
     ("functional inversion" "finv" "functional inversion @{H}" t "functional\\s-+inversion")
     ("generalize dependent" "gd" "generalize dependent #" t "generalize\\s-+dependent")
     ("generalize" "g" "generalize #" t "generalize")
     ("hnf" "hnf" "hnf" t "hnf")
     ("idtac" "id" "idtac" nil "idtac") ; also in tacticals with abbrev id
     ("idtac \"" "id\"" "idtac \"#\"")  ; also in tacticals
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
     ("lazy" "lazy" "lazy beta delta [#] iota zeta" t "lazy")
     ("lazymatch with" "m" "lazymatch # with\n| # => #\nend")
     ("left" "left" "left" t "left")
     ("lia" nil "lia" t "lia")
     ("linear" "lin" "linear" t "linear")
     ("load" "load" "load" t "load")
     ("lra" nil "lra" t "lra")
     ("move after" "mov" "move # after #" t "move")
     ("multimatch with" "m" "multimatch # with\n| # => #\nend")
     ("nia" nil "nia" t "nia")
     ("now_show" nil "now_show" t "now_show")
     ("nra" nil "nra" t "nra")
     ("nsatz" nil "nsatz" t "nsatz")
     ("omega" "o" "omega" t "omega")
     ("pattern" "pat" "pattern" t "pattern")
     ("pattern(s)" "pats" "pattern # , #" t)
     ("pattern at" "pata" "pattern # at #" t)
     ("pose" "po" "pose ( # := # )" t "pose")
     ("prolog" "prol" "prolog" t "prolog")
     ("psatz" nil "psatz" t "psatz")
     ("quote" "quote" "quote" t "quote")
     ("quote []" "quote2" "quote # [#]" t)
     ("red" "red" "red" t "red")
     ("refine" "ref" "refine" t "refine")
     ;;      ("reflexivity" "refl" "reflexivity #" t "reflexivity")
     ("rename into" "ren" "rename # into #" t "rename")
     ("replace with" "rep" "replace # with #" t "replace")
     ("replace with in" "repi" "replace # with # in #" t)
     ("revert dependent" "r" "revert dependent" t "revert\\s-+dependent")
     ("revert" "r" "revert" t "revert")
     ("rewrite_all" nil "rewrite_all" t "rewrite_all")
     ("rewrite_all <-" nil "rewrite_all" t "rewrite_all")
     ("rewrite <- in" "ri<" "rewrite <- # in #" t)
     ("rewrite <-" "r<" "rewrite <- #" t)
     ("rewrite in" "ri" "rewrite # in #" t)
     ("rewrite" "r" "rewrite #" t "rewrite")
     ("right" "rig" "right" t "right")
     ;;      ("ring" "ring" "ring #" t "ring")
     ("romega" nil "romega" t "romega")
     ("set in * |-" "seth" "set ( # := #) in * |-" t)
     ("set in *" "set*" "set ( # := #) in *" t)
     ("set in |- *" "setg" "set ( # := #) in |- *" t)
     ("set in" "seti" "set ( # := #) in #" t)
     ("set" "set" "set ( # := #)" t "set")
     ("setoid_replace with" "strep2" "setoid_replace # with #" t "setoid_replace")
     ("setoid replace with" "strep" "setoid replace # with #" t "setoid\\s-+replace")
     ("setoid_rewrite" "strew" "setoid_rewrite #" t "setoid_rewrite")
     ("setoid rewrite" "strew" "setoid rewrite #" t "setoid\\s-+rewrite")
     ("simpl" "s" "simpl" t "simpl")
     ("simpl at" "sa" "simpl # at #" t)
     ("simpl (all flags)" "simpl" "simpl beta delta [#] iota zeta" t)
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
     ("symmetry in" "syi" "symmetry in #" t)
     ;;    ("tauto" "ta" "tauto" t "tauto")
     ("transitivity" "trans" "transitivity #" t "transitivity")
     ("trivial" "t" "trivial" t "trivial")
     ("trivial with" "tw" "trivial with @{db}" t)
     ("unfold" "u" "unfold #" t "unfold")
     ("unfold(s)" "us" "unfold # , #" t)
     ("unfold in" "unfi" "unfold # in #" t)
     ("unfold at" "unfa" "unfold # at #" t)
     ("vm_compute" "vmc" "vm_compute." t "vm_compute")
     ;; SSReflect tactics.
     ("nat_congr" "ncongr"  "nat_congr" t "nat_congr")
     ("nat_norm" "nnorm"  "nat_norm" t "nat_norm")
     ("bool_congr" "bcongr"  "bool_congr" t "bool_congr")
     ("prop_congr" "prcongr"  "prop_congr" t "prop_congr")
     ("move" "m"  "move" t "move")
     ("pose" "po"  "pose # := #" t "pose")
     ("set" "set"  "set # := #" t "set")
     ("have" "hv" "have # : #" t "have")
     ("congr" "con" "congr #" t "congr")
     ("wlog" "wlog" "wlog : / #" t "wlog")
     ("without loss" "wilog" "without loss #" t "without loss")
     ("unlock" "unlock" "unlock #" t "unlock")
     ("suffices" "suffices" "suffices # : #" t "suffices")
     ("suff" "suff" "suff # : #" t "suff")
     )
   coq-user-tactics-db)
  "Coq tactics information list. See `coq-syntax-db' for syntax. "
  )

;; user shortcuts are prioritized by being put at the end
(defvar coq-solve-tactics-db
  (append
   '(
     ("assumption" "as" "assumption" t "assumption")
     ("eassumption" "eas" "eassumption" t "eassumption")
     ("easy" nil "easy" t "easy")
     ("now" nil "now" t "now")
     ("by" "by" "by #" t "by")
     ("congruence" "cong" "congruence" t "congruence")
     ("contradict" "contr" "contradict" t "contradict")
     ("contradiction" "contr" "contradiction" t "contradiction")
     ("decide equality" "deg" "decide equality" t "decide\\s-+equality")
     ("discriminate" "dis" "discriminate" t "discriminate")
     ("exact" "exa" "exact" t "exact")
     ("fourier" "four" "fourier" t "fourier")
     ("fail" "fa" "fail" nil)
     ("field" "field" "field" t "field")
     ("gfail" "gfa" "gfail" nil "gfail")
     ("lia" nil "lia" t "lia")
     ("lra" nil "lra" t "lra")
     ("nia" nil "nia" t "nia")
     ("nra" nil "nra" t "nra")
     ("nsatz" nil "nsatz" t "nsatz")
     ("omega" "o" "omega" t "omega")
     ("romega" nil "romega" t "romega")
     ("psatz" nil "psatz" t "psatz")
     ("reflexivity" "refl" "reflexivity #" t "reflexivity")
     ("ring" "ring" "ring #" t "ring")
     ("solve" nil "solve [ # | # ]" nil "solve")
     ("tauto" "ta" "tauto" t "tauto")
     ;; SSReflect solving tactics.
     ("done" nil "done" nil "done")
     )
   coq-user-solve-tactics-db)
  "Coq tactic(al)s that solve a subgoal."
  )

(defvar coq-solve-cheat-tactics-db
  (append
   '(("admit" nil "admit" t "admit")
     ("Admitted" nil "Admitted" t "Admitted"))
   coq-user-cheat-tactics-db)
  "Coq tactic(al)s that solve a subgoal."
  )

;; FIXME is this needed?
(defvar develock-coq-font-lock-keywords
  '((develock-find-long-lines
     (1 'develock-long-line-1 t)
     (2 'develock-long-line-2 t))
    ("[^	\n ]\\([	 ]+\\)$"
     (1 'develock-whitespace-1 t))
    ("^[	 ]+$"
     (0 'develock-whitespace-2 append))
    ("\\.[{}]" 0 'develock-whitespace-2 nil nil)))


(defvar coq-tacticals-db
  (append
   '(
     ("info" nil "info #" nil "info")
     ("first" nil "first [ # | # ]" nil "first")
     ("abstract" nil "abstract @{tac} using @{name}." nil "abstract")
     ("do" nil "do @{num} @{tac}" nil "do")
     ("idtac" nil "idtac")              ; also in tactics
                                        ;    ("idtac \"" nil "idtac \"#\"") ; also in tactics
     ("fail" "fa" "fail" nil "fail")
                                        ;    ("fail \"" "fa\"" "fail" nil) ;
                                        ;    ("orelse" nil "orelse #" t "orelse")
     ("repeat" nil "repeat #" nil "repeat")
     ("try" nil "try #" nil "try")
     ("tryif" "tryif" "tryif # then # else #" nil "tryif")
     ("progress" nil "progress #" nil "progress")
     ("|" nil "[ # | # ]" nil)
     ("||" nil "# || #" nil)
     ;; SSReflect tacticals.
     ("last" "lst" nil t "last")
     )
   coq-user-tacticals-db)
  "Coq tacticals information list.  See `coq-syntax-db' for syntax.")




(defvar coq-decl-db
  '(
    ("Local Axiom" nil "Local Axiom # : #" t "Local\\s-+Axiom")
    ("Local Axioms" nil "Local Axioms # , #: #" t "Local\\s-+Axioms")
    ("Axiom" "ax" "Axiom # : #" t "Axiom")
    ("Axioms" "axs" "Axioms # , #: #" t "Axioms")
    ("Global Variable" "gv" "Global Variable #: #." t "Global\\s-+Variable")
    ("Global Variables" "gvs" "Global Variables # , #: #." t "Global\\s-+Variables")
    ("Hint Constructors" "hc" "Hint Constructors # : #." t "Hint\\s-+Constructors")
    ("Hint Extern" "he" "Hint Extern @{cost} @{pat} => @{tac} : @{db}." t "Hint\\s-+Extern")
    ("Hint Immediate" "hi" "Hint Immediate # : @{db}." t "Hint\\s-+Immediate")
    ("Hint Resolve" "hr" "Hint Resolve # : @{db}." t "Hint\\s-+Resolve")
    ("Hint Rewrite ->" "hrw" "Hint Rewrite -> @{t1,t2...} using @{tac} : @{db}." t "Hint\\s-+Rewrite")
    ("Hint Rewrite <-" "hrw" "Hint Rewrite <- @{t1,t2...} using @{tac} : @{db}." t )
    ("Hint Unfold" "hu" "Hint Unfold # : #." t "Hint\\s-+Unfold")
    ("Existing Class" nil "Existing Class " t "Existing\\s-+Class")
    ("Existing Instance" nil "Existing Instance " t "Existing\\s-+Instance")
    ("Existing Instances" nil "Existing Instances " t "Existing\\s-+Instances")
    ("Hypothesis" "hyp" "Hypothesis #: #" t "Hypothesis")
    ("Hypotheses" "hyp" "Hypotheses #: #" t "Hypotheses")
    ("Parameter" "par" "Parameter #: #" t "Parameter")
    ("Parameters" "par" "Parameters #: #" t "Parameters")
    ("Conjecture" "conj" "Conjecture #: #." t "Conjecture")
    ("Variable" "v" "Variable #: #." t "Variable")
    ("Variables" "vs" "Variables # , #: #." t "Variables")
    ("Context" nil "Context #, (# : #)." t "Context")
    ("Local Coercion" nil "Local Coercion @{id} : @{typ1} >-> @{typ2}." t "Local\\s-+Coercion")
    ("Coercion" "coerc" "Coercion @{id} : @{typ1} >-> @{typ2}." t "Coercion")
    )
  "Coq declaration keywords information list. See `coq-syntax-db' for syntax."
  )

(defvar coq-defn-db
  '(
    ("CoFixpoint" "cfix" "CoFixpoint # (#:#) : # :=\n#." t "CoFixpoint")
    ("CoInductive" "coindv" "CoInductive # : # :=\n|# : #." t "CoInductive")
    ("Class" "class" "Class [ # ] := \n# : #;\n# : #." t "Class")
    ("Declare Module : :=" "dm" "Declare Module # : # := #." t "Declare\\s-+Module")
    ("Declare Module <: :=" "dm2" "Declare Module # <: # := #." t);; careful
    ("Declare Module Import : :=" "dmi" "Declare Module # : # := #." t)
    ("Declare Module Import <: :=" "dmi2" "Declare Module # <: # := #." t);; careful
    ("Declare Module Export : :=" "dme" "Declare Module # : # := #." t)
    ("Declare Module Export <: :=" "dme2" "Declare Module # <: # := #." t);; careful
    ("Local Definition" nil "Local Definition #:# := #." t "Local\\s-+Definition");; careful
    ("Definition" "def" "Definition #:# := #." t "Definition");; careful
    ("Definition (2 args)" "def2" "Definition # (# : #) (# : #):# := #." t)
    ("Definition (3 args)" "def3" "Definition # (# : #) (# : #) (# : #):# := #." t)
    ("Definition (4 args)" "def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." t)
    ("Program Definition" "pdef" "Program Definition #:# := #." t "Program\\s-+Definition");; careful ?
    ("Program Definition (2 args)" "pdef2" "Program Definition # (# : #) (# : #):# := #." t)
    ("Program Definition (3 args)" "pdef3" "Program Definition # (# : #) (# : #) (# : #):# := #." t)
    ("Program Definition (4 args)" "pdef4" "Program Definition # (# : #) (# : #) (# : #) (# : #):# := #." t)
    ("Derive Inversion" nil "Derive Inversion @{id} with # Sort #." t "Derive\\s-+Inversion")
    ("Derive Dependent Inversion" nil "Derive Dependent Inversion @{id} with # Sort #." t "Derive\\s-+Dependent\\s-+Inversion")
    ("Derive Inversion_clear" nil "Derive Inversion_clear @{id} with # Sort #." t)
    ("Example" "ex" "Example #:# := #." t "Example");; careful
    ("Equations" "eqs" "Equations #:# := #." t "Equations")
    ("Fixpoint" "fix" "Fixpoint # (#:#) {struct @{arg}} : # :=\n#." t "Fixpoint")
    ("Program Fixpoint" "pfix" "Program Fixpoint # (#:#) {struct @{arg}} : # :=\n#." t "Program\\s-+Fixpoint")
    ("Program Fixpoint measure" "pfixm" "Program Fixpoint # (#:#) {measure @{arg} @{f}} : # :=\n#." t)
    ("Program Fixpoint wf" "pfixwf" "Program Fixpoint # (#:#) {wf @{arg} @{f}} : # :=\n#." t)
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
    ("Instance" nil "Instance #:#.\nProof.\n#Defined." t "Instance")
    ("Program Instance" "pinstance" "Program Instance [ # ] => # where \n# := #;\n# := #." t "Program\\s-+Instance")
    ("Let" "Let" "Let # : # := #." t "Let")
    ("Local Ltac" nil "Local Ltac # := #" t "Local\\s-+Ltac")
    ("Ltac" "ltac" "Ltac # := #" t "Ltac")
    ("Module :=" "mo" "Module # : # := #." t ) ; careful
    ("Module <: :=" "mo2" "Module # <: # := #." t ) ; careful
    ("Module Import :=" "moi" "Module Import # : # := #." t ) ; careful
    ("Module Import <: :=" "moi2" "Module Import # <: # := #." t ) ; careful
    ("Module Export :=" "moe" "Module Export # : # := #." t ) ; careful
    ("Module Export <: :=" "moe2" "Module Export# <: # := #." t ) ; careful
    ("Record" "rec" "Record # : # := {\n# : #;\n# : # }" t "Record")
    ("Scheme" "sc" "Scheme @{name} := #." t "Scheme")
    ("Scheme Induction" "sci" "Scheme @{name} := Induction for # Sort #." t)
    ("Scheme Minimality" "scm" "Scheme @{name} := Minimality for # Sort #." t)
    ("Structure" "str" "Structure # : # := {\n# : #;\n# : # }" t "Structure")
    )
  "Coq definition keywords information list. See `coq-syntax-db' for syntax. "
  )

;; modules and section are indented like goal starters
;;; PC TODO: this category is used only for indentation, because
;;; scripting uses information from coq to decide if a goal is
;;; started. Since it is impossible for some commands to know
;;; syntactically if they start something (ex: Instance), the
;;; right thing to do would be to indent only on "Proof." and forget
;;; about this category for indentation.

(defvar coq-goal-starters-db
  '(
     ("Add Morphism" "addmor" "Add Morphism @{f} : @{id}" t "Add\\s-+Morphism")
     ("Add Parametric Morphism" nil "Add Parametric Morphism : " t "Add\\s-+Parametric\\s-+Morphism")
    ("Chapter" "chp" "Chapter # : #." t "Chapter")
    ("Corollary" "cor" "Corollary # : #.\nProof.\n#\nQed." t "Corollary")
    ("Declare Module :" "dmi" "Declare Module # : #.\n#\nEnd #." t)
    ("Declare Module <:" "dmi2" "Declare Module # <: #.\n#\nEnd #." t)
    ("Definition goal" "defg" "Definition #:#.\n#\nDefined." t);; careful
    ("Fact" "fct" "Fact # : #." t "Fact")
    ("Goal" nil "Goal #." t "Goal")
    ("Instance goal" "instg" "Instance #:#.\n#\nDefined." t);; careful
    ("Lemma" "l" "Lemma # : #.\nProof.\n#\nQed." t "Lemma")
    ("Program Lemma" "pl" "Program Lemma # : #.\nProof.\n#\nQed." t "Program\\s-+Lemma")
    ("Proposition" "l" "Proposition # : #.\nProof.\n#\nQed." t "Proposition")
    ("Module! (interactive)" nil "Module # : #.\n#\nEnd #." nil nil coq-insert-section-or-module)
    ("Module Type" "mti" "Module Type #.\n#\nEnd #." t "Module\\s-+Type") ; careful
    ("Module :" "moi" "Module # : #.\n#\nEnd #." t "Module") ; careful
    ("Module <:" "moi2" "Module # <: #.\n#\nEnd #." t ) ; careful
    ("Remark" "rk" "Remark # : #.\n#\nQed." t "Remark")
    ("Section" "sec" "Section #." t "Section")
    ("Theorem" "th" "Theorem # : #.\n#\nQed." t "Theorem")
    ("Program Theorem" "pth" "Program Theorem # : #.\nProof.\n#\nQed." t "Program\\s-+Theorem")
    ("Obligation" "obl" "Obligation #.\n#\nQed." t "Obligation")
    ("Obligations" "obls" "Obligations #.\n#\nQed." nil "Obligations")
    ("Next Obligation" "nobl" "Next Obligation.\n#\nQed." t "Next Obligation")
    )
  "Coq goal starters keywords information list. See `coq-syntax-db' for syntax. "
  )

;; TODO: dig other queries from the refman.
;; Extraction command may go here
;; all Print, Show and Test stuff
;; Some of the Set/Unset (like Set Printing All, Set Extraction Inline etc)
(defvar coq-queries-commands-db
   '(
     ("About" nil "About #." nil "About")
     ("Check" nil "Check" nil "Check")
     ("Fail" nil "Fail" nil "fail")
     ("Inspect" nil "Inspect #." nil "Inspect")
     ("Locate File" nil "Locate File \"#\"." nil "Locate\\s-+File")
     ("Locate Library" nil "Locate Library #." nil "Locate\\s-+Library")
     ("Locate Notation" nil "Locate Notation (#) #" nil "Locate\\s-+Notation")
     ("Locate" nil "Locate" nil "Locate")
     ("Print Coercions" nil "Print Coercions." nil "Print\\s-+Coercions")
     ("Print Hint" nil "Print Hint." nil "Print\\s-+Hint" coq-PrintHint)
     ("Print" "p" "Print #." nil "Print")
     ("Pwd" nil "Pwd." nil "Pwd")
     ("Search" nil "Search #" nil "Search")
     ("SearchAbout" nil "SearchAbout #" nil "SearchAbout")
     ("SearchPattern" nil "SearchPattern (#)" nil "SearchPattern")
     ("SearchRewrite" nil "SearchRewrite #" nil "SearchRewrite")
     ("Show" nil "Show #." nil "Show")
     ("Test" nil "Test" nil "Test" nil t) ; let us not highlight all possible options for Test
     ("Timeout" nil "Timeout" nil "Timeout")
     )
   "Coq queries command, that deserve a separate menu for sending them to coq without insertion. "
   )

;; command that are not declarations, definition or goal starters
(defvar coq-other-commands-db
  '(
    ("Add Parametric Relation" nil "Add Parametric Relation : " t "Add\\s-+Parametric\\s-+Relation")
    ;; ("Abort" nil "Abort." t "Abort" nil nil);don't appear in menu
    ;; ("Add" nil "Add #." nil "Add" nil t)
    ("Add Abstract Ring" nil "Add Abstract Ring #." t "Add\\s-+Abstract\\s-+Ring")
    ("Add Abstract Semi Ring" nil "Add Abstract Semi Ring #." t "Add\\s-+Abstract\\s-+Semi\\s-+Ring")
    ("Add Field" nil "Add Field #." t "Add\\s-+Field")
    ("Add LoadPath" nil "Add LoadPath #." nil "Add\\s-+LoadPath")
    ("Add ML Path" nil "Add ML Path #." nil "Add\\s-+ML\\s-+Path")
    ("Add Printing" nil "Add Printing #." t "Add\\s-+Printing")
    ("Add Printing If" nil "Add Printing If #." t "Add\\s-+Printing\\s-+If")
    ("Add Printing Let" nil "Add Printing Let #." t "Add\\s-+Printing\\s-+Let")
    ("Add Rec LoadPath" nil "Add Rec LoadPath #." nil "Add\\s-+Rec\\s-+LoadPath")
    ("Add Rec ML Path" nil "Add Rec ML Path #." nil "Add\\s-+Rec\\s-+ML\\s-+Path")
    ("Add Ring" nil "Add Ring #." t "Add\\s-+Ring")
    ("Add Semi Ring" nil "Add Semi Ring #." t "Add\\s-+Semi\\s-+Ring")
    ("Add Setoid" nil "Add Setoid #." t "Add\\s-+Setoid")
    ("Admit Obligations" "oblsadmit" "Admit Obligations." nil "Admit\\s-+Obligations")
    ("Arguments Scope" "argsc" "Arguments Scope @{id} [ @{_} ]" t "Arguments\\s-+Scope")
    ("Local Arguments" nil "Local Arguments @{id} : @{rule}" t "Local\\s-+Arguments")
    ("Arguments" "args" "Arguments @{id} : @{rule}" t "Arguments")
    ("Bind Scope" "bndsc" "Bind Scope @{scope} with @{type}" t "Bind\\s-+Scope")
    ("Canonical Structure" nil "Canonical Structure #." t "Canonical\\s-+Structure")
    ("Cd" nil "Cd #." nil "Cd")
    ("Local Close Scope" "lclsc" "Local Close Scope #" t "Local\\s-+Close\\s-+Scope")
    ("Close Scope" "clsc" "Close Scope #" t "Close\\s-+Scope")
    ("Comments" nil "Comments #." nil "Comments")
    ("Declare" nil "Declare #." nil "Declare")
    ("Delimit Scope" "delsc" "Delimit Scope @{scope} with @{id}." t "Delimit\\s-+Scope" )
    ("Eval" nil "Eval #." nil "Eval")
    ("Export" nil "Export #." t "Export")
    ("Extract Constant" "extrc" "Extract Constant @{id} => \"@{id}\"." nil "Extract\\s-+Constant")
    ("Extract Inlined Constant" "extric" "Extract Inlined Constant @{id} => \"@{id}\"." nil "Extract\\s-+Inlined\\s-+Constant")
    ("Extract Inductive" "extri" "Extract Inductive @{id} => \"@{id}\" [\"@{id}\" \"@{id...}\"]." nil "Extract")
    ("Extraction (in a file)" "extrf" "Extraction \"@{file}\" @{id}." nil)
    ("Extraction Inline" nil "Extraction Inline #." t "Extraction\\s-+Inline")
    ("Extraction NoInline" nil "Extraction NoInline #." t "Extraction\\s-+NoInline")
    ("Extraction Language" "extrlang" "Extraction Language #." t "Extraction\\s-+Language")
    ("Extraction Library" "extrl" "Extraction Library @{id}." nil "Extraction\\s-+Library")
    ("Extraction" "extr" "Extraction @{id}." nil "Extraction")
    ("Focus" nil "Focus #." nil "Focus")
    ("Generalizable Variables" nil "Generalizable Variables #." t "Generalizable\\s-+Variables")
    ("Generalizable All Variables" nil "Generalizable All Variables." t "Generalizable\\s-+All\\s-+Variables")
    ("Identity Coercion" nil "Identity Coercion #." t "Identity\\s-+Coercion")
    ("Implicit Arguments Off" nil "Implicit Arguments Off." t "Implicit\\s-+Arguments\\s-+Off")
    ("Implicit Arguments On" nil "Implicit Arguments On." t "Implicit\\s-+Arguments\\s-+On")
    ("Implicit Arguments" nil "Implicit Arguments # [#]." t "Implicit\\s-+Arguments")
    ("Implicit Types" nil "Implicit Types # : #." t "Implicit\\s-+Types")
    ("Import" nil "Import #." t "Import")
    ("Include" nil "Include #." t "Include")
    ("Infix" "inf" "Infix \"#\" := # (at level #) : @{scope}." t "Infix")
    ("Notation (assoc)" "notas" "Notation \"#\" := # (at level #, # associativity)." t)
    ("Notation (at assoc)" "notassc" "Notation \"#\" := # (at level #, # associativity) : @{scope}." t)
    ("Notation (at at scope)" "notasc" "Notation \"#\" := # (at level #, # at level #) : @{scope}." t)
    ("Notation (at at)" "nota" "Notation \"#\" := # (at level #, # at level #)." t)
    ("Notation (only parsing)" "notsp" "Notation # := # (only parsing)." t)
    ("Local Notation" "lnots" "Local Notation # := #." t "Local\\s-+Notation")
    ("Local Notation (only parsing)" "lnotsp" "Local Notation # := # (only parsing)." t)
    ("Notation (simple)" "nots" "Notation # := #." t "Notation")
    ("Typeclasses Opaque" nil "Typeclasses Opaque #." nil "Typeclasses\\s-+Opaque")
    ("Opaque" nil "Opaque #." nil "Opaque")
    ("Obligation Tactic" nil "Obligation Tactic := #." t "Obligation\\s-+Tactic")
    ("Local Open Scope" nil "Local Open Scope #" t "Local\\s-+Open\\s-+Scope")
    ("Open Local Scope" nil "Open Local Scope #" t "Open\\s-+Local\\s-+Scope")
    ("Open Scope" "opsc" "Open Scope #" t "Open\\s-+Scope")
    ("Preterm" nil "Preterm." nil "Preterm")
    ("Qed" nil "Qed." nil "Qed")
    ("Recursive Extraction" "recextr" "Recursive Extraction @{id}." nil "Recursive\\s-+Extraction")
    ("Recursive Extraction Library" "recextrl" "Recursive Extraction Library @{id}." nil "Recursive\\s-+Extraction\\s-+Library")
    ("Recursive Extraction Module" "recextrm" "Recursive Extraction Module @{id}." nil "Recursive\\s-+Extraction\\s-+Module")
    ("Remove LoadPath" nil "Remove LoadPath" nil "Remove\\s-+LoadPath")
    ("Remove LoadPath" nil "Remove LoadPath" nil "Remove\\s-+LoadPath")
    ("Remove Printing If" nil "Remove Printing If #." t "Remove\\s-+Printing\\s-+If")
    ("Remove Printing Let" nil "Remove Printing Let #." t "Remove\\s-+Printing\\s-+Let")
    ("Require Export" nil "Require Export #." t "Require\\s-+Export")
    ("Require Import" nil "Require Import #." t "Require\\s-+Import")
    ("Require" nil "Require #." t "Require")
    ("Reserved Infix" nil "Reserved Infix" nil "Reserved\\s-+Infix")
    ("Reserved Notation" nil "Reserved Notation" nil "Reserved\\s-+Notation")
    ("Reset Extraction Inline" nil "Reset Extraction Inline." t "Reset\\s-+Extraction\\s-+Inline")
    ("Save" nil "Save." t "Save")
    ("Set Asymmetric Patterns" nil "Set Asymmetric Patterns" t "Set Asymmetric\\s-+Patterns")
    ("Set Atomic Load" nil "Set Atomic Load" t "Set Atomic\\s-+Load")
    ("Set Automatic Coercions Import" nil "Set Automatic Coercions Import" t "Set Automatic\\s-+Coercions\\s-+Import")
    ("Set Automatic Introduction" nil "Set Automatic Introduction" t "Set Automatic\\s-+Introduction")
    ("Set Boolean Equality Schemes" nil "Set Boolean Equality Schemes" t "Set Boolean\\s-+Equality\\s-+Schemes")
    ("Set Bracketing Last Introduction Pattern" nil "Set Bracketing Last Introduction Pattern" t "Set Bracketing\\s-+Last\\s-+Introduction\\s-+Pattern")
    ("Set Bullet Behavior" nil "Set Bullet Behavior" t "Set Bullet\\s-+Behavior")
    ("Set Case Analysis Schemes" nil "Set Case Analysis Schemes" t "Set Case\\s-+Analysis\\s-+Schemes")
    ("Set Compat Notations" nil "Set Compat Notations" t "Set Compat\\s-+Notations")
    ("Set Congruence Depth" nil "Set Congruence Depth" t "Set Congruence\\s-+Depth")
    ("Set Congruence Verbose" nil "Set Congruence Verbose" t "Set Congruence\\s-+Verbose")
    ("Set Contextual Implicit" nil "Set Contextual Implicit" t "Set Contextual\\s-+Implicit")
    ("Set Debug Auto" nil "Set Debug Auto" t "Set Debug\\s-+Auto")
    ("Set Debug Eauto" nil "Set Debug Eauto" t "Set Debug\\s-+Eauto")
    ("Set Debug RAKAM" nil "Set Debug RAKAM" t "Set Debug\\s-+RAKAM")
    ("Set Debug Tactic Unification" nil "Set Debug Tactic Unification" t "Set Debug\\s-+Tactic\\s-+Unification")
    ("Set Debug Trivial" nil "Set Debug Trivial" t "Set Debug\\s-+Trivial")
    ("Set Debug Unification" nil "Set Debug Unification" t "Set Debug\\s-+Unification")
    ("Set Decidable Equality Schemes" nil "Set Decidable Equality Schemes" t "Set Decidable\\s-+Equality\\s-+Schemes")
    ("Set Default Clearing Used Hypotheses" nil "Set Default Clearing Used Hypotheses" t "Set Default\\s-+Clearing\\s-+Used\\s-+Hypotheses")
    ("Set Default Goal Selector" nil "Set Default Goal Selector" t "Set Default\\s-+Goal\\s-+Selector")
    ("Set Default Proof Mode" nil "Set Default Proof Mode" t "Set Default\\s-+Proof\\s-+Mode")
    ("Set Default Proof Using" nil "Set Default Proof Using" t "Set Default\\s-+Proof\\s-+Using")
    ("Set Default Timeout" nil "Set Default Timeout" t "Set Default\\s-+Timeout")
    ("Set Dependent Propositions Elimination" nil "Set Dependent Propositions Elimination" t "Set Dependent\\s-+Propositions\\s-+Elimination")
    ("Set Discriminate Introduction" nil "Set Discriminate Introduction" t "Set Discriminate\\s-+Introduction")
    ("Set Dump Bytecode" nil "Set Dump Bytecode" t "Set Dump\\s-+Bytecode")
    ("Set Elimination Schemes" nil "Set Elimination Schemes" t "Set Elimination\\s-+Schemes")
    ("Set Equality Scheme" nil "Set Equality Scheme" t "Set Equality\\s-+Scheme")
    ("Set Extraction AccessOpaque" nil "Set Extraction AccessOpaque" t "Set Extraction\\s-+AccessOpaque")
    ("Set Extraction AutoInline" nil "Set Extraction AutoInline" t "Set Extraction\\s-+AutoInline")
    ("Set Extraction Conservative Types" nil "Set Extraction Conservative Types" t "Set Extraction\\s-+Conservative\\s-+Types")
    ("Set Extraction File Comment" nil "Set Extraction File Comment" t "Set Extraction\\s-+File\\s-+Comment")
    ("Set Extraction Flag" nil "Set Extraction Flag" t "Set Extraction\\s-+Flag")
    ("Set Extraction KeepSingleton" nil "Set Extraction KeepSingleton" t "Set Extraction\\s-+KeepSingleton")
    ("Set Extraction Optimize" nil "Set Extraction Optimize" t "Set Extraction\\s-+Optimize")
    ("Set Extraction SafeImplicits" nil "Set Extraction SafeImplicits" t "Set Extraction\\s-+SafeImplicits")
    ("Set Extraction TypeExpand" nil "Set Extraction TypeExpand" t "Set Extraction\\s-+TypeExpand")
    ("Set Firstorder Depth" nil "Set Firstorder Depth" t "Set Firstorder\\s-+Depth")
    ("Set Hide Obligations" nil "Set Hide Obligations" t "Set Hide\\s-+Obligations")
    ("Set Implicit Arguments" nil "Set Implicit Arguments" t "Set Implicit\\s-+Arguments")
    ("Set Info Auto" nil "Set Info Auto" t "Set Info\\s-+Auto")
    ("Set Info Eauto" nil "Set Info Eauto" t "Set Info\\s-+Eauto")
    ("Set Info Level" nil "Set Info Level" t "Set Info\\s-+Level")
    ("Set Info Trivial" nil "Set Info Trivial" t "Set Info\\s-+Trivial")
    ("Set Injection L2R Pattern Order" nil "Set Injection L2R Pattern Order" t "Set Injection\\s-+L2R\\s-+Pattern\\s-+Order")
    ("Set Injection On Proofs" nil "Set Injection On Proofs" t "Set Injection\\s-+On\\s-+Proofs")
    ("Set Inline Level" nil "Set Inline Level" t "Set Inline\\s-+Level")
    ("Set Intuition Iff Unfolding" nil "Set Intuition Iff Unfolding" t "Set Intuition\\s-+Iff\\s-+Unfolding")
    ("Set Intuition Negation Unfolding" nil "Set Intuition Negation Unfolding" t "Set Intuition\\s-+Negation\\s-+Unfolding")
    ("Set Kernel Term Sharing" nil "Set Kernel Term Sharing" t "Set Kernel\\s-+Term\\s-+Sharing")
    ("Set Keyed Unification" nil "Set Keyed Unification" t "Set Keyed\\s-+Unification")
    ("Set Loose Hint Behavior" nil "Set Loose Hint Behavior" t "Set Loose\\s-+Hint\\s-+Behavior")
    ("Set Maximal Implicit Insertion" nil "Set Maximal Implicit Insertion" t "Set Maximal\\s-+Implicit\\s-+Insertion")
    ("Set Nonrecursive Elimination Schemes" nil "Set Nonrecursive Elimination Schemes" t "Set Nonrecursive\\s-+Elimination\\s-+Schemes")
    ("Set Parsing Explicit" nil "Set Parsing Explicit" t "Set Parsing\\s-+Explicit")
    ("Set Primitive Projections" nil "Set Primitive Projections" t "Set Primitive\\s-+Projections")
    ("Set Printing All" nil "Set Printing All" t "Set\\s-+Printing\\s-+All")
    ("Set Printing Coercions" nil "Set Printing Coercions" t "Set\\s-+Printing\\s-+Coercions")
    ("Set Printing Compact Contexts" nil "Set Printing Compact Contexts" t "Set\\s-+Printing\\s-+Compact\\s-+Contexts")
    ("Set Printing Depth" nil "Set Printing Depth" t "Set\\s-+Printing\\s-+Depth")
    ("Set Printing Existential Instances" nil "Set Printing Existential Instances" t "Set\\s-+Printing\\s-+Existential\\s-+Instances")
    ("Set Printing Goal Tags" nil "Set Printing Goal Tags" t "Set\\s-+Printing\\s-+Goal\\s-+Tags")
    ("Set Printing Goal Names" nil "Set Printing Goal Names" t "Set\\s-+Printing\\s-+Goal\\s-+Names")
    ("Set Printing Implicit" nil "Set Printing Implicit" t "Set\\s-+Printing\\s-+Implicit")
    ("Set Printing Implicit Defensive" nil "Set Printing Implicit Defensive" t "Set\\s-+Printing\\s-+Implicit\\s-+Defensive")
    ("Set Printing Matching" nil "Set Printing Matching" t "Set\\s-+Printing\\s-+Matching")
    ("Set Printing Notations" nil "Set Printing Notations" t "Set\\s-+Printing\\s-+Notations")
    ("Set Printing Primitive Projection Compatibility" nil "Set Printing Primitive Projection Compatibility" t "Set\\s-+Printing\\s-+Primitive\\s-+Projection\\s-+Compatibility")
    ("Set Printing Primitive Projection Parameters" nil "Set Printing Primitive Projection Parameters" t "Set\\s-+Printing\\s-+Primitive\\s-+Projection\\s-+Parameters")
    ("Set Printing Projections" nil "Set Printing Projections" t "Set\\s-+Printing\\s-+Projections")
    ("Set Printing Records" nil "Set Printing Records" t "Set\\s-+Printing\\s-+Records")
    ("Set Printing Synth" nil "Set Printing Synth" t "Set\\s-+Printing\\s-+Synth")
    ("Set Printing Unfocused" nil "Set Printing Unfocused" t "Set\\s-+Printing\\s-+Unfocused")
    ("Set Printing Universes" nil "Set Printing Universes" t "Set\\s-+Printing\\s-+Universes")
    ("Set Printing Width" nil "Set Printing Width" t "Set\\s-+Printing\\s-+Width")
    ("Set Printing Wildcard" nil "Set Printing Wildcard" t "Set\\s-+Printing\\s-+Wildcard")
    ("Set Program Mode" nil "Set Program Mode" t "Set Program\\s-+Mode")
    ("Set Proof Using Clear Unused" nil "Set Proof Using Clear Unused" t "Set Proof\\s-+Using\\s-+Clear\\s-+Unused")
    ("Set Record Elimination Schemes" nil "Set Record Elimination Schemes" t "Set Record\\s-+Elimination\\s-+Schemes")
    ("Set Refine Instance Mode" nil "Set Refine Instance Mode" t "Set Refine\\s-+Instance\\s-+Mode")
    ("Set Regular Subst Tactic" nil "Set Regular Subst Tactic" t "Set Regular\\s-+Subst\\s-+Tactic")
    ("Set Reversible Pattern Implicit" nil "Set Reversible Pattern Implicit" t "Set Reversible\\s-+Pattern\\s-+Implicit")
    ("Set Rewriting Schemes" nil "Set Rewriting Schemes" t "Set Rewriting\\s-+Schemes")
    ("Set Short Module Printing" nil "Set Short Module Printing" t "Set Short\\s-+Module\\s-+Printing")
    ("Set Shrink Obligations" nil "Set Shrink Obligations" t "Set Shrink\\s-+Obligations")
    ("Set SimplIsCbn" nil "Set SimplIsCbn" t "Set SimplIsCbn")
    ("Set Standard Proposition Elimination Names" nil "Set Standard Proposition Elimination Names" t "Set Standard\\s-+Proposition\\s-+Elimination\\s-+Names")
    ("Set Strict Proofs" nil "Set Strict Proofs" t "Set Strict\\s-+Proofs")
    ("Set Strict Universe Declaration" nil "Set Strict Universe Declaration" t "Set Strict\\s-+Universe\\s-+Declaration")
    ("Set Strongly Strict Implicit" nil "Set Strongly Strict Implicit" t "Set Strongly\\s-+Strict\\s-+Implicit")
    ("Set Suggest Proof Using" nil "Set Suggest Proof Using" t "Set Suggest\\s-+Proof\\s-+Using")
    ("Set Tactic Compat Context" nil "Set Tactic Compat Context" t "Set Tactic\\s-+Compat\\s-+Context")
    ("Set Tactic Evars Pattern Unification" nil "Set Tactic Evars Pattern Unification" t "Set Tactic\\s-+Evars\\s-+Pattern\\s-+Unification")
    ("Set Tactic Pattern Unification" nil "Set Tactic Pattern Unification" t "Set Tactic\\s-+Pattern\\s-+Unification")
    ("Set Transparent Obligations" nil "Set Transparent Obligations" t "Set Transparent\\s-+Obligations")
    ("Set Typeclass Resolution After Apply" nil "Set Typeclass Resolution After Apply" t "Set Typeclass\\s-+Resolution\\s-+After\\s-+Apply")
    ("Set Typeclass Resolution For Conversion" nil "Set Typeclass Resolution For Conversion" t "Set Typeclass\\s-+Resolution\\s-+For\\s-+Conversion")
    ("Set Typeclasses Debug" nil "Set Typeclasses Debug" t "Set Typeclasses\\s-+Debug")
    ("Set Typeclasses Dependency Order" nil "Set Typeclasses Dependency Order" t "Set Typeclasses\\s-+Dependency\\s-+Order")
    ("Set Typeclasses Depth" nil "Set Typeclasses Depth" t "Set Typeclasses\\s-+Depth")
    ("Set Typeclasses Modulo Eta" nil "Set Typeclasses Modulo Eta" t "Set Typeclasses\\s-+Modulo\\s-+Eta")
    ("Set Typeclasses Strict Resolution" nil "Set Typeclasses Strict Resolution" t "Set Typeclasses\\s-+Strict\\s-+Resolution")
    ("Set Typeclasses Unique Instances" nil "Set Typeclasses Unique Instances" t "Set Typeclasses\\s-+Unique\\s-+Instances")
    ("Set Typeclasses Unique Solutions" nil "Set Typeclasses Unique Solutions" t "Set Typeclasses\\s-+Unique\\s-+Solutions")
    ("Set Universal Lemma Under Conjunction" nil "Set Universal Lemma Under Conjunction" t "Set Universal\\s-+Lemma\\s-+Under\\s-+Conjunction")
    ("Set Universe Minimization ToSet" nil "Set Universe Minimization ToSet" t "Set Universe\\s-+Minimization\\s-+ToSet")
    ("Set Universe Polymorphism" nil "Set Universe Polymorphism" t "Set Universe\\s-+Polymorphism")
    ("Set Verbose Compat Notations" nil "Set Verbose Compat Notations" t "Set Verbose\\s-+Compat\\s-+Notations")
    ("Set Function_debug" nil "Set Function_debug" t "Set Function_debug")
    ("Set Function_raw_tcc" nil "Set Function_raw_tcc" t "Set Function_raw_tcc")
    ("Set Functional Induction Rewrite Dependent" nil "Set Functional Induction Rewrite Dependent" t "Set Functional\\s-+Induction\\s-+Rewrite\\s-+Dependent")
    ("Set Hyps Limit" nil "Set Hyps Limit" t "Set Hyps\\s-+Limit")
    ("Set Ltac Debug" nil "Set Ltac Debug" t "Set Ltac\\s-+Debug")
    ("Set Silent" nil "Set Silent" t "Set Silent")
    ("Set Undo" nil "Set Undo" t "Set Undo")
    ("Set Search Blacklist" nil "Set Search Blacklist" t "Set Search\\s-+Blacklist")
    ("Set Printing Coercion" nil "Set Printing Coercion" t "Set\\s-+Printing\\s-+Coercion")
    ("Set Printing If" nil "Set Printing If" t "Set\\s-+Printing\\s-+If")
    ("Set Printing Let" nil "Set Printing Let" t "Set\\s-+Printing\\s-+Let")
    ("Set Printing Record" nil "Set Printing Record" t "Set\\s-+Printing\\s-+Record")
    ("Set Printing Constructor" nil "Set Printing Constructor" t "Set\\s-+Printing\\s-+Constructor")
    ("Solve Obligations" "oblssolve" "Solve Obligations using #." t "Solve\\s-+Obligations")
    ("Local Strategy" nil "Local Strategy # [#]." t "Local\\s-+Strategy")
    ("Strategy" nil "Strategy # [#]." t "Strategy")
    ("Tactic Notation" nil "Tactic Notation # := #." t "Tactic\\s-+Notation")
    ("Transparent" nil "Transparent #." nil "Transparent")

    ("Unfocus" nil "Unfocus." nil "Unfocus")
    ("Unset Asymmetric Patterns" nil "Unset Asymmetric Patterns" t "Unset Asymmetric\\s-+Patterns")
    ("Unset Atomic Load" nil "Unset Atomic Load" t "Unset Atomic\\s-+Load")
    ("Unset Automatic Coercions Import" nil "Unset Automatic Coercions Import" t "Unset Automatic\\s-+Coercions\\s-+Import")
    ("Unset Automatic Introduction" nil "Unset Automatic Introduction" t "Unset Automatic\\s-+Introduction")
    ("Unset Boolean Equality Schemes" nil "Unset Boolean Equality Schemes" t "Unset Boolean\\s-+Equality\\s-+Schemes")
    ("Unset Bracketing Last Introduction Pattern" nil "Unset Bracketing Last Introduction Pattern" t "Unset Bracketing\\s-+Last\\s-+Introduction\\s-+Pattern")
    ("Unset Bullet Behavior" nil "Unset Bullet Behavior" t "Unset Bullet\\s-+Behavior")
    ("Unset Case Analysis Schemes" nil "Unset Case Analysis Schemes" t "Unset Case\\s-+Analysis\\s-+Schemes")
    ("Unset Compat Notations" nil "Unset Compat Notations" t "Unset Compat\\s-+Notations")
    ("Unset Congruence Depth" nil "Unset Congruence Depth" t "Unset Congruence\\s-+Depth")
    ("Unset Congruence Verbose" nil "Unset Congruence Verbose" t "Unset Congruence\\s-+Verbose")
    ("Unset Contextual Implicit" nil "Unset Contextual Implicit" t "Unset Contextual\\s-+Implicit")
    ("Unset Debug Auto" nil "Unset Debug Auto" t "Unset Debug\\s-+Auto")
    ("Unset Debug Eauto" nil "Unset Debug Eauto" t "Unset Debug\\s-+Eauto")
    ("Unset Debug RAKAM" nil "Unset Debug RAKAM" t "Unset Debug\\s-+RAKAM")
    ("Unset Debug Tactic Unification" nil "Unset Debug Tactic Unification" t "Unset Debug\\s-+Tactic\\s-+Unification")
    ("Unset Debug Trivial" nil "Unset Debug Trivial" t "Unset Debug\\s-+Trivial")
    ("Unset Debug Unification" nil "Unset Debug Unification" t "Unset Debug\\s-+Unification")
    ("Unset Decidable Equality Schemes" nil "Unset Decidable Equality Schemes" t "Unset Decidable\\s-+Equality\\s-+Schemes")
    ("Unset Default Clearing Used Hypotheses" nil "Unset Default Clearing Used Hypotheses" t "Unset Default\\s-+Clearing\\s-+Used\\s-+Hypotheses")
    ("Unset Default Goal Selector" nil "Unset Default Goal Selector" t "Unset Default\\s-+Goal\\s-+Selector")
    ("Unset Default Proof Mode" nil "Unset Default Proof Mode" t "Unset Default\\s-+Proof\\s-+Mode")
    ("Unset Default Proof Using" nil "Unset Default Proof Using" t "Unset Default\\s-+Proof\\s-+Using")
    ("Unset Default Timeout" nil "Unset Default Timeout" t "Unset Default\\s-+Timeout")
    ("Unset Dependent Propositions Elimination" nil "Unset Dependent Propositions Elimination" t "Unset Dependent\\s-+Propositions\\s-+Elimination")
    ("Unset Discriminate Introduction" nil "Unset Discriminate Introduction" t "Unset Discriminate\\s-+Introduction")
    ("Unset Dump Bytecode" nil "Unset Dump Bytecode" t "Unset Dump\\s-+Bytecode")
    ("Unset Elimination Schemes" nil "Unset Elimination Schemes" t "Unset Elimination\\s-+Schemes")
    ("Unset Equality Scheme" nil "Unset Equality Scheme" t "Unset Equality\\s-+Scheme")
    ("Unset Extraction AccessOpaque" nil "Unset Extraction AccessOpaque" t "Unset Extraction\\s-+AccessOpaque")
    ("Unset Extraction AutoInline" nil "Unset Extraction AutoInline" t "Unset Extraction\\s-+AutoInline")
    ("Unset Extraction Conservative Types" nil "Unset Extraction Conservative Types" t "Unset Extraction\\s-+Conservative\\s-+Types")
    ("Unset Extraction File Comment" nil "Unset Extraction File Comment" t "Unset Extraction\\s-+File\\s-+Comment")
    ("Unset Extraction Flag" nil "Unset Extraction Flag" t "Unset Extraction\\s-+Flag")
    ("Unset Extraction KeepSingleton" nil "Unset Extraction KeepSingleton" t "Unset Extraction\\s-+KeepSingleton")
    ("Unset Extraction Optimize" nil "Unset Extraction Optimize" t "Unset Extraction\\s-+Optimize")
    ("Unset Extraction SafeImplicits" nil "Unset Extraction SafeImplicits" t "Unset Extraction\\s-+SafeImplicits")
    ("Unset Extraction TypeExpand" nil "Unset Extraction TypeExpand" t "Unset Extraction\\s-+TypeExpand")
    ("Unset Firstorder Depth" nil "Unset Firstorder Depth" t "Unset Firstorder\\s-+Depth")
    ("Unset Hide Obligations" nil "Unset Hide Obligations" t "Unset Hide\\s-+Obligations")
    ("Unset Implicit Arguments" nil "Unset Implicit Arguments" t "Unset Implicit\\s-+Arguments")
    ("Unset Info Auto" nil "Unset Info Auto" t "Unset Info\\s-+Auto")
    ("Unset Info Eauto" nil "Unset Info Eauto" t "Unset Info\\s-+Eauto")
    ("Unset Info Level" nil "Unset Info Level" t "Unset Info\\s-+Level")
    ("Unset Info Trivial" nil "Unset Info Trivial" t "Unset Info\\s-+Trivial")
    ("Unset Injection L2R Pattern Order" nil "Unset Injection L2R Pattern Order" t "Unset Injection\\s-+L2R\\s-+Pattern\\s-+Order")
    ("Unset Injection On Proofs" nil "Unset Injection On Proofs" t "Unset Injection\\s-+On\\s-+Proofs")
    ("Unset Inline Level" nil "Unset Inline Level" t "Unset Inline\\s-+Level")
    ("Unset Intuition Iff Unfolding" nil "Unset Intuition Iff Unfolding" t "Unset Intuition\\s-+Iff\\s-+Unfolding")
    ("Unset Intuition Negation Unfolding" nil "Unset Intuition Negation Unfolding" t "Unset Intuition\\s-+Negation\\s-+Unfolding")
    ("Unset Kernel Term Sharing" nil "Unset Kernel Term Sharing" t "Unset Kernel\\s-+Term\\s-+Sharing")
    ("Unset Keyed Unification" nil "Unset Keyed Unification" t "Unset Keyed\\s-+Unification")
    ("Unset Loose Hint Behavior" nil "Unset Loose Hint Behavior" t "Unset Loose\\s-+Hint\\s-+Behavior")
    ("Unset Maximal Implicit Insertion" nil "Unset Maximal Implicit Insertion" t "Unset Maximal\\s-+Implicit\\s-+Insertion")
    ("Unset Nonrecursive Elimination Schemes" nil "Unset Nonrecursive Elimination Schemes" t "Unset Nonrecursive\\s-+Elimination\\s-+Schemes")
    ("Unset Parsing Explicit" nil "Unset Parsing Explicit" t "Unset Parsing\\s-+Explicit")
    ("Unset Primitive Projections" nil "Unset Primitive Projections" t "Unset Primitive\\s-+Projections")
    ("Unset Printing All" nil "Unset Printing All" t "Unset Printing\\s-+All")
    ("Unset Printing Coercions" nil "Unset Printing Coercions" t "Unset Printing\\s-+Coercions")
    ("Unset Printing Depth" nil "Unset Printing Depth" t "Unset Printing\\s-+Depth")
    ("Unset Printing Existential Instances" nil "Unset Printing Existential Instances" t "Unset Printing\\s-+Existential\\s-+Instances")
    ("Unset Printing Implicit" nil "Unset Printing Implicit" t "Unset Printing\\s-+Implicit")
    ("Unset Printing Implicit Defensive" nil "Unset Printing Implicit Defensive" t "Unset Printing\\s-+Implicit\\s-+Defensive")
    ("Unset Printing Matching" nil "Unset Printing Matching" t "Unset Printing\\s-+Matching")
    ("Unset Printing Notations" nil "Unset Printing Notations" t "Unset Printing\\s-+Notations")
    ("Unset Printing Primitive Projection Compatibility" nil "Unset Printing Primitive Projection Compatibility" t "Unset Printing\\s-+Primitive\\s-+Projection\\s-+Compatibility")
    ("Unset Printing Primitive Projection Parameters" nil "Unset Printing Primitive Projection Parameters" t "Unset Printing\\s-+Primitive\\s-+Projection\\s-+Parameters")
    ("Unset Printing Projections" nil "Unset Printing Projections" t "Unset Printing\\s-+Projections")
    ("Unset Printing Records" nil "Unset Printing Records" t "Unset Printing\\s-+Records")
    ("Unset Printing Synth" nil "Unset Printing Synth" t "Unset Printing\\s-+Synth")
    ("Unset Printing Universes" nil "Unset Printing Universes" t "Unset Printing\\s-+Universes")
    ("Unset Printing Width" nil "Unset Printing Width" t "Unset Printing\\s-+Width")
    ("Unset Printing Wildcard" nil "Unset Printing Wildcard" t "Unset Printing\\s-+Wildcard")
    ("Unset Program Mode" nil "Unset Program Mode" t "Unset Program\\s-+Mode")
    ("Unset Proof Using Clear Unused" nil "Unset Proof Using Clear Unused" t "Unset Proof\\s-+Using\\s-+Clear\\s-+Unused")
    ("Unset Record Elimination Schemes" nil "Unset Record Elimination Schemes" t "Unset Record\\s-+Elimination\\s-+Schemes")
    ("Unset Refine Instance Mode" nil "Unset Refine Instance Mode" t "Unset Refine\\s-+Instance\\s-+Mode")
    ("Unset Regular Subst Tactic" nil "Unset Regular Subst Tactic" t "Unset Regular\\s-+Subst\\s-+Tactic")
    ("Unset Reversible Pattern Implicit" nil "Unset Reversible Pattern Implicit" t "Unset Reversible\\s-+Pattern\\s-+Implicit")
    ("Unset Rewriting Schemes" nil "Unset Rewriting Schemes" t "Unset Rewriting\\s-+Schemes")
    ("Unset Short Module Printing" nil "Unset Short Module Printing" t "Unset Short\\s-+Module\\s-+Printing")
    ("Unset Shrink Obligations" nil "Unset Shrink Obligations" t "Unset Shrink\\s-+Obligations")
    ("Unset SimplIsCbn" nil "Unset SimplIsCbn" t "Unset SimplIsCbn")
    ("Unset Standard Proposition Elimination Names" nil "Unset Standard Proposition Elimination Names" t "Unset Standard\\s-+Proposition\\s-+Elimination\\s-+Names")
    ("Unset Strict Proofs" nil "Unset Strict Proofs" t "Unset Strict\\s-+Proofs")
    ("Unset Strict Universe Declaration" nil "Unset Strict Universe Declaration" t "Unset Strict\\s-+Universe\\s-+Declaration")
    ("Unset Strongly Strict Implicit" nil "Unset Strongly Strict Implicit" t "Unset Strongly\\s-+Strict\\s-+Implicit")
    ("Unset Suggest Proof Using" nil "Unset Suggest Proof Using" t "Unset Suggest\\s-+Proof\\s-+Using")
    ("Unset Tactic Compat Context" nil "Unset Tactic Compat Context" t "Unset Tactic\\s-+Compat\\s-+Context")
    ("Unset Tactic Evars Pattern Unification" nil "Unset Tactic Evars Pattern Unification" t "Unset Tactic\\s-+Evars\\s-+Pattern\\s-+Unification")
    ("Unset Tactic Pattern Unification" nil "Unset Tactic Pattern Unification" t "Unset Tactic\\s-+Pattern\\s-+Unification")
    ("Unset Transparent Obligations" nil "Unset Transparent Obligations" t "Unset Transparent\\s-+Obligations")
    ("Unset Typeclass Resolution After Apply" nil "Unset Typeclass Resolution After Apply" t "Unset Typeclass\\s-+Resolution\\s-+After\\s-+Apply")
    ("Unset Typeclass Resolution For Conversion" nil "Unset Typeclass Resolution For Conversion" t "Unset Typeclass\\s-+Resolution\\s-+For\\s-+Conversion")
    ("Unset Typeclasses Debug" nil "Unset Typeclasses Debug" t "Unset Typeclasses\\s-+Debug")
    ("Unset Typeclasses Dependency Order" nil "Unset Typeclasses Dependency Order" t "Unset Typeclasses\\s-+Dependency\\s-+Order")
    ("Unset Typeclasses Depth" nil "Unset Typeclasses Depth" t "Unset Typeclasses\\s-+Depth")
    ("Unset Typeclasses Modulo Eta" nil "Unset Typeclasses Modulo Eta" t "Unset Typeclasses\\s-+Modulo\\s-+Eta")
    ("Unset Typeclasses Strict Resolution" nil "Unset Typeclasses Strict Resolution" t "Unset Typeclasses\\s-+Strict\\s-+Resolution")
    ("Unset Typeclasses Unique Instances" nil "Unset Typeclasses Unique Instances" t "Unset Typeclasses\\s-+Unique\\s-+Instances")
    ("Unset Typeclasses Unique Solutions" nil "Unset Typeclasses Unique Solutions" t "Unset Typeclasses\\s-+Unique\\s-+Solutions")
    ("Unset Universal Lemma Under Conjunction" nil "Unset Universal Lemma Under Conjunction" t "Unset Universal\\s-+Lemma\\s-+Under\\s-+Conjunction")
    ("Unset Universe Minimization ToUnset" nil "Unset Universe Minimization ToUnset" t "Unset Universe\\s-+Minimization\\s-+ToUnset")
    ("Unset Universe Polymorphism" nil "Unset Universe Polymorphism" t "Unset Universe\\s-+Polymorphism")
    ("Unset Verbose Compat Notations" nil "Unset Verbose Compat Notations" t "Unset Verbose\\s-+Compat\\s-+Notations")
    ("Unset Function_debug" nil "Unset Function_debug" t "Unset Function_debug")
    ("Unset Function_raw_tcc" nil "Unset Function_raw_tcc" t "Unset Function_raw_tcc")
    ("Unset Functional Induction Rewrite Dependent" nil "Unset Functional Induction Rewrite Dependent" t "Unset Functional\\s-+Induction\\s-+Rewrite\\s-+Dependent")
    ("Unset Hyps Limit" nil "Unset Hyps Limit" t "Unset Hyps\\s-+Limit")
    ("Unset Ltac Debug" nil "Unset Ltac Debug" t "Unset Ltac\\s-+Debug")
    ("Unset Silent" nil "Unset Silent" t "Unset Silent")
    ("Unset Undo" nil "Unset Undo" t "Unset Undo")
    ("Unset Search Blacklist" nil "Unset Search Blacklist" t "Unset Search\\s-+Blacklist")
    ("Unset Printing Coercion" nil "Unset Printing Coercion" t "Unset Printing\\s-+Coercion")
    ("Unset Printing If" nil "Unset Printing If" t "Unset Printing\\s-+If")
    ("Unset Printing Let" nil "Unset Printing Let" t "Unset Printing\\s-+Let")
    ("Unset Printing Record" nil "Unset Printing Record" t "Unset Printing\\s-+Record")
    ("Unset Printing Constructor" nil "Unset Printing Constructor" t "Unset Printing\\s-+Constructor")
                                        ;    ("print" "pr" "print #" "print")
    )
   "Command that are not declarations, definition or goal starters."
  )


(defvar coq-ssreflect-commands-db
  '(("Unset Strict Implicit" "unsti" nil t "Strict\\s-+Implicit")
    ("Prenex Implicits" "pi" "Prenex Implicits #" t "Prenex\\s-+Implicits")
    ("Hint View for" "hv" "Hint View for #" t "Hint\\s-+View\\s-+for")))

(defvar coq-commands-db
  (append coq-decl-db coq-defn-db coq-goal-starters-db
          coq-queries-commands-db
          coq-other-commands-db coq-ssreflect-commands-db coq-user-commands-db)
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
;;*) suivant les suggestions de Chritine, pas de mode preuve dans un type de
;;    module (donc pas de Definition truc:machin.  Lemma, Theorem ... )
;;
;; *) la commande Module M [ ( : | <: ) MTYP ] [ := MEXPR ] est valable
;;    uniquement hors d'un MT
;;    - si :=MEXPR est absent, elle demarre un nouveau module interactif
;;    - si :=MEXPR est present, elle definit un module
;;    (la fonction vernac_define_module dans toplevel/vernacentries)
;;
;; *) la nouvelle commande Declare Module M [ ( : | <: ) MTYP ] [ := MEXPR ]
;;    est valable uniquement dans un MT
;;    - si :=MEXPR absent, :MTYP absent, elle demarre un nouveau module
;;      interactif
;;    - si (:=MEXPR absent, :MTYP present)
;;      ou (:=MEXPR present, :MTYP absent)
;;      elle declare un module.
;;    (la fonction vernac_declare_module dans toplevel/vernacentries)

(defun coq-count-match (regexp strg)
  "Count the number of (maximum, non overlapping) matching substring
 of STRG matching REGEXP. Empty match are counted once."
  (let ((nbmatch 0) (str strg))
    (while (and (proof-string-match regexp str) (not (string-equal str "")))
      (incf nbmatch)
      (if (= (match-end 0) 0) (setq str (substring str 1))
        (setq str (substring str (match-end 0)))))
    nbmatch))

;; Module and or section openings are detected syntactically. Module
;; *openings* are difficult to detect because there can be Module
;; ...with X := ... . So we need to count :='s to detect real openings.

;; TODO: have opened section/chapter in the prompt too, and get rid of
;; syntactical tests everywhere
(defun coq-module-opening-p (str)
  "Decide whether STR is a module or section opening or not.
Used by `coq-goal-command-p'"
  (let* ((match (coq-count-match "\\_<match\\_>" str))
         (with (coq-count-match "\\_<with\\_>" str))
         (letwith (+ (coq-count-match "\\_<let\\_>" str) (- with match)))
         (affect (coq-count-match ":=" str)))
    (and (proof-string-match "\\`\\(Module\\)\\_>" str)
         (= letwith affect))))

(defun coq-section-command-p (str)
  (proof-string-match "\\`\\(Section\\|Chapter\\)\\_>" str))

;; unused anymore (for good)
(defun coq-goal-command-str-p (str)
  "Decide syntactically whether STR is a goal start or not. Use
`coq-goal-command-p' on a span instead if possible."
  (let* ((match (coq-count-match "\\_<match\\_>" str))
         (with (- (coq-count-match "\\_<with\\_>" str) (coq-count-match "\\_<with\\s-+signature\\_>" str)))
         (letwith (+ (coq-count-match "\\_<let\\_>" str) (- with match)))
         (affect (coq-count-match ":=" str)))
    (and (proof-string-match coq-goal-command-regexp str)
         (not
          (and
           (proof-string-match
            (concat "\\`\\(Local\\|Definition\\|Lemma\\|Theorem\\|Fact\\|Add\\|Let\\|Program\\|Module\\|Class\\|Instance\\)\\_>")
            str)
           (not (= letwith affect))))
         (not (proof-string-match "\\`Declare\\s-+Module\\(\\w\\|\\s-\\|<\\)*:"
                                  str)))))

;; This is the function that tests if a SPAN is a goal start. All it
;; has to do is look at the 'goalcmd attribute of the span.
;; It also looks if this is not a module start.

;; TODO: have also attributes 'modulecmd and 'sectioncmd. This needs
;; something in the coq prompt telling the name of all opened modules
;; (like for open goals), and use it to set goalcmd --> no more need
;; to look at Modules and section (actually indentation will still
;; need it)
(defun coq-goal-command-p (span)
  "see `coq-goal-command-p'"
  (or (span-property span 'goalcmd)
      ;; module and section starts are detected here
      (let ((str (or (span-property span 'cmd) "")))
        (or (coq-section-command-p str)
            (coq-module-opening-p str)))))

;; TODO: rely on coq response nistead for span grouping Or better have
;; coq change its syntax for something better.
(defvar coq-keywords-save-strict
  '("Defined" "Save" "Qed" "End" "Admitted" "Abort" )
  "This regexp must match *exactly* commands that close a goal/Module.
It is used:
 1) for grouping spans into one when scripting
 2) for indentation.")

(defvar coq-keywords-save
  (append coq-keywords-save-strict '("Proof"))
  )


(defun coq-save-command-p (span str)
  "Decide whether argument is a Save command or not"
  (or (proof-string-match coq-save-command-regexp-strict str)
      (and (proof-string-match "\\`Proof\\_>" str)
           (not (proof-string-match "\\`Proof\\s-*\\(\\.\\|\\_<with\\_>\\|\\_<using\\_>\\)" str)))))


;; ----- keywords for font-lock.

(defvar coq-keywords-kill-goal
  '("Abort"))

;; Following regexps are all state changing
(defvar coq-keywords-state-changing-misc-commands
  (coq-build-regexp-list-from-db coq-commands-db 'filter-state-changing))

(defvar coq-keywords-goal
  (coq-build-regexp-list-from-db coq-goal-starters-db))

(defvar coq-keywords-decl
  (coq-build-regexp-list-from-db coq-decl-db))

(defvar coq-keywords-defn
  (coq-build-regexp-list-from-db coq-defn-db))


(defvar coq-keywords-state-changing-commands
  (append
   coq-keywords-state-changing-misc-commands
   coq-keywords-decl                    ; all state changing
   coq-keywords-defn                    ; idem
   coq-keywords-goal))                  ; idem


;;
(defvar coq-keywords-state-preserving-commands
  (coq-build-regexp-list-from-db coq-commands-db 'filter-state-preserving))

;; concat this is faster that redoing coq-build-regexp-list-from-db on
;; whole commands-db
(defvar coq-keywords-commands
  (append coq-keywords-state-changing-commands
	  coq-keywords-state-preserving-commands)
  "All commands keyword.")

(defvar coq-solve-tactics
  (coq-build-regexp-list-from-db coq-solve-tactics-db)
  "Keywords for closing tactic(al)s.")

(defvar coq-solve-tactics-regexp
  (coq-build-opt-regexp-from-db coq-solve-tactics-db)
  "Keywords regexp for closing tactic(al)s.")

(defvar coq-solve-cheat-tactics
  (coq-build-regexp-list-from-db coq-solve-cheat-tactics-db)
  "Keywords for closing by cheating tactic(al)s.")

(defvar coq-solve-cheat-tactics-regexp
  (coq-build-opt-regexp-from-db coq-solve-cheat-tactics-db)
  "Keywords regexp for closing by cheating tactic(al)s.")

(defvar coq-tacticals
  (coq-build-regexp-list-from-db coq-tacticals-db)
  "Keywords for tacticals in a Coq script.")

(defvar coq-symbol-binders "∀\\|∃\\|λ")



 ;; From JF Monin:
(defvar coq-reserved
  (append
   '(
     "False" "True" "after" "as" "cofix" "fix" "forall" "fun" "match"
     "lazymatch" "multimatch"
     "return" "struct" "else" "end" "if" "in" "into" "let" "then"
     "using" "with" "beta" "delta" "iota" "zeta" "after" "until"
     "at" "Sort" "Time" "dest" "where"
     ;; SSReflect user reserved.
     "is" "nosimpl" "of")
   coq-user-reserved-db)
  "Reserved keywords of Coq.")

;; FIXME: ∀ and ∃ should be followed by a space in coq syntax.
;; FIXME: actually these are not exactly reserved keywords, find
;; another classification of keywords.
(defvar coq-reserved-regexp
  (concat "\\_<with\\s-+signature\\_>\\|"
   (proof-ids-to-regexp coq-reserved)))

(defvar coq-state-changing-tactics
  (coq-build-regexp-list-from-db coq-tactics-db 'filter-state-changing))

(defvar coq-state-preserving-tactics
  (coq-build-regexp-list-from-db coq-tactics-db 'filter-state-preserving))


(defvar coq-tactics
  (append coq-state-changing-tactics coq-state-preserving-tactics))

(defvar coq-tactics-regexp (coq-build-opt-regexp-from-db coq-tactics-db))
;(defvar coq-tactics-regexp-symb (coq-build-opt-regexp-from-db coq-tactics-db))

(defvar coq-retractable-instruct
  (append coq-state-changing-tactics coq-keywords-state-changing-commands))

(defvar coq-non-retractable-instruct
  (append coq-state-preserving-tactics
          coq-keywords-state-preserving-commands))

(defvar coq-keywords
  (append coq-keywords-goal coq-keywords-save coq-keywords-decl
	  coq-keywords-defn coq-keywords-commands)
  "All keywords in a Coq script.")

;; coq-build-opt-regexp-from-db already adds "\\_<" "\\_>"
(defun proof-regexp-alt-list-symb (args)
  (concat "\\_<\\(?:" (proof-regexp-alt-list args) "\\)\\_>"))

(defvar coq-keywords-regexp (proof-regexp-alt-list-symb coq-keywords))


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
    "==>"
    "++>"
    "@"
    "->"
    "."
    "∧"
    "∨"
    "→"
    "\\/"
    "/\\"
    "->")
  "Punctuation Symbols used by Coq.")

(defvar coq-symbols-regexp (regexp-opt coq-symbols))

;; ----- regular expressions
(defvar coq-error-regexp "^\\(In nested Ltac call\\|Error:\\|Discarding pattern\\|Syntax error:\\|System Error:\\|User Error:\\|User error:\\|Anomaly[:.]\\|Toplevel input[,]\\)"
  "A regexp indicating that the Coq process has identified an error.")

;; april2017: coq-8.7 removes special chars definitely and puts
;; <infomsg> and <warning> around all messages except errors.
;; We let our legacy regexp for some years and remove them, say, in 2020.
(defvar coq-shell-eager-annotation-start
   "\376\\|\\[Reinterning\\|Warning:\\|TcDebug \\|<infomsg>\\|<warning>")

(defvar coq-shell-eager-annotation-end
  "\377\\|done\\]\\|</infomsg>\\|</warning>\\|\\*\\*\\*\\*\\*\\*\\|) >")

(defvar coq-id "\\(@\\|_\\|\\w\\)\\(\\w\\|\\s_\\)*") ;; Coq ca start an id with @ or _
(defvar coq-id-shy "\\(?:@\\|_\\|\\w\\)\\(?:\\w\\|\\s_\\)*")

; do not use proof-ids with a space separator!
(defvar coq-ids (concat coq-id "\\(" "\\s-+" coq-id "\\)*"))

(defun coq-first-abstr-regexp (paren end)
  (concat paren "\\s-*\\(" coq-ids "\\)\\s-*" end))

(defcustom coq-variable-highlight-enable t
  "Activates partial bound variable highlighting"
  :type 'boolean
  :group 'coq)

(defcustom coq-symbol-highlight-enable nil
  "Activates partial bound variable highlighting"
  :type 'boolean
  :group 'coq)

(defconst coq-lambda-regexp "\\(?:\\_<fun\\_>\\|λ\\)")

(defconst coq-forall-regexp "\\(?:\\_<forall\\_>\\|∀\\)")
(defconst coq-exists-regexp "\\(?:\\_<exists\\_>\\|∃\\)")

(defvar coq-font-lock-terms
  (append
   (list ;; flattened by append above
    (cons coq-symbol-binders 'coq-symbol-binder-face))
   (when coq-symbol-highlight-enable
     (list (cons coq-symbols-regexp 'coq-symbol-face)))
   (when coq-variable-highlight-enable
     (list
      ;; lambda binders
      (list (coq-first-abstr-regexp coq-lambda-regexp "\\(?:=>\\|:\\|,\\)") 1 'font-lock-variable-name-face)
      ;; forall binder
      (list (coq-first-abstr-regexp coq-forall-regexp "\\(?:,\\|:\\)") 1 'font-lock-variable-name-face)
      (list (coq-first-abstr-regexp coq-exists-regexp "\\(?:,\\|:\\)") 1 'font-lock-variable-name-face)
      ;;   (list "\\<forall\\>"
      ;;         (list 0 font-lock-type-face)
      ;;         (list (concat "[^ :]\\s-*\\(" coq-ids "\\)\\s-*") nil nil
      ;;               (list 0 font-lock-variable-name-face)))
      ;; parenthesized binders
      (list (coq-first-abstr-regexp "(" ":[ a-zA-Z]") 1 'font-lock-variable-name-face)
      (list (coq-first-abstr-regexp "{" ":[ a-zA-Z]") 1 'font-lock-variable-name-face)
      )))
  "*Font-lock table for Coq terms.")



;; According to Coq, "Definition" is both a declaration and a goal.
;; It is understood here as being a goal.  This is important for
;; recognizing global identifiers, see coq-global-p.
(defconst coq-save-command-regexp-strict
  (proof-anchor-regexp
   (concat "\\(?:Time\\s-+\\)?\\(" (proof-ids-to-regexp coq-keywords-save-strict)
           "\\)")))


(defconst coq-save-command-regexp
  (proof-anchor-regexp
   (concat "\\(?:Time\\s-+\\)?\\(" (proof-ids-to-regexp coq-keywords-save)
           "\\)")))

(defconst coq-save-with-hole-regexp
  (concat "\\(?:Time\\s-+\\)?\\(" (proof-regexp-alt-list coq-keywords-save-strict)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*\\."))

(defconst coq-goal-command-regexp
  (proof-anchor-regexp (proof-regexp-alt-list coq-keywords-goal)))

(defconst coq-goal-with-hole-regexp
  (concat "\\(" (proof-regexp-alt-list coq-keywords-goal)
	  "\\)\\s-+\\(" coq-id "\\)\\s-*:?"))

(defconst coq-decl-with-hole-regexp
  (concat "\\(" (proof-regexp-alt-list coq-keywords-decl)
	  "\\)\\s-+\\(" coq-ids "\\)\\s-*:"))

;;  (defconst coq-decl-with-hole-regexp
;;    (if coq-variable-highlight-enable coq-decl-with-hole-regexp-1 'nil))

(defconst coq-defn-with-hole-regexp
  (concat "\\(" (proof-regexp-alt-list coq-keywords-defn)
          "\\)\\s-+\\(" coq-id "\\)"))

;; must match:
;; "with f x y :" (followed by = or not)
;; "with f x y (z:" (not followed by =)
;; BUT NOT:
;; "with f ... (x:="
;; "match ... with .. => "
(defconst coq-with-with-hole-regexp
  (concat "\\(with\\)\\s-+\\(" coq-id "\\)\\s-*\\([^=(.]*:\\|[^(]*(\\s-*"
          coq-id "\\s-*:[^=]\\)"))
;; marche aussi a peu pres
;;  (concat "\\(with\\)\\s-+\\(" coq-id "\\)\\s-*\\([^(.]*:\\|.*)[^(.]*:=\\)"))
;;"\\<Prop\\>\\|\\<Set\\>\\|\\<Type\\>"


(defconst coq-context-marker-regexp
  (concat (regexp-opt '("ltac" "constr" "uconstr") 'symbols) ":"))

;;
;; font-lock
;;
(defvar coq-font-lock-keywords-1
  (append
   coq-font-lock-terms
   `((,coq-solve-tactics-regexp . 'coq-solve-tactics-face)
     (,coq-solve-cheat-tactics-regexp . 'coq-cheat-face)
     (,coq-keywords-regexp . 'font-lock-keyword-face)
     (,coq-reserved-regexp . 'font-lock-type-face)
     (,coq-tactics-regexp . 'proof-tactics-name-face)
     (,(proof-regexp-alt-list coq-tacticals) . 'proof-tacticals-name-face)
     (,(proof-regexp-alt-list-symb (list "Set" "Type" "Prop")) . 'font-lock-type-face)
     ("============================" . 'font-lock-keyword-face)
     (,coq-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (,coq-context-marker-regexp 1 'coq-context-qualifier-face))
   (if coq-variable-highlight-enable
       `((,coq-decl-with-hole-regexp 2 'font-lock-variable-name-face)))
   `((,coq-defn-with-hole-regexp 2 'font-lock-function-name-face)
     (,coq-with-with-hole-regexp 2 'font-lock-function-name-face)
     (,coq-save-with-hole-regexp 2 'font-lock-function-name-face)
     ;; Remove spurious variable and function faces on commas.
     (proof-zap-commas))))


;; ", " is for multiple hypothesis displayed in v8.5. If more than
;; 1 space this is a hypothesis displayed in the middle of a line (> v8.5)
;; "^    " is for goals in debug mode.
(defvar coq-hyp-name-in-goal-or-response-regexp
    "\\(^\\|^  \\|^    \\|[^^ ] ?  \\)\\(\\(?:[^\n :(),=]\\|, \\)+ *\\(?::[ \n]\\|,$\\)\\)"
  "regexp matching hypothesis names in goal or response buffer")

;; We define a slightly different set of keywords for response buffer.

(defvar coq-response-font-lock-keywords
  (append
   coq-font-lock-terms
   (list
    (cons coq-reserved-regexp 'font-lock-type-face)
    (cons coq-keywords-regexp 'font-lock-keyword-face)
    (cons coq-shell-eager-annotation-start 'proof-warning-face)
    (cons coq-error-regexp 'proof-error-face)
    (cons (proof-regexp-alt-list-symb (list "In environment" "The term" "has type")) 'proof-error-face)
    (cons (proof-regexp-alt-list-symb (list "Set" "Type" "Prop")) 'font-lock-type-face)
    (list (concat "[?]" coq-id) 0 'coq-question-mark-face) ;; highlight evars and Ltac variables
    (list coq-hyp-name-in-goal-or-response-regexp 2 'proof-declaration-name-face)
    (list "^\\([^ \n]+\\) \\(is defined\\)" (list 1 'font-lock-function-name-face t)))))

(defvar coq-goals-font-lock-keywords
  (append
   coq-font-lock-terms
   (list
    (cons coq-reserved-regexp 'font-lock-type-face)
    (list (concat "[?]" coq-id) 0 'coq-question-mark-face) ;; highlight evars and Ltac variables
    (list coq-hyp-name-in-goal-or-response-regexp 2 'proof-declaration-name-face)
    (cons (proof-regexp-alt-list-symb (list "Set" "Type" "Prop")) 'font-lock-type-face))))



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
  (modify-syntax-entry ?_  "_") ; beware: word consituent EXCEPT in head position
  (modify-syntax-entry ?\' "_") ; always word constituent
  (modify-syntax-entry ?∀ ".")
  (modify-syntax-entry ?∃ ".")
  (modify-syntax-entry ?λ ".") ;; maybe a bad idea... lambda is a letter
  (modify-syntax-entry ?\| ".")

  ;; should maybe be "_" but it makes coq-find-and-forget (in coq.el) bug
  ;; Hence the coq-with-altered-syntax-table below to put "." into "_" class temporarily
  (modify-syntax-entry ?\. ".")

  (modify-syntax-entry ?\* ". 23n")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

;; use this to evaluate code with "." being consisdered a symbol
;; constituent (better behavior for thing-at and maybe font-lock too,
;; for indentation we use ad hoc smie lexers).
(defmacro coq-with-altered-syntax-table (&rest code)
  (declare (debug t))
  (let ((res (make-symbol "res")))
    `(unwind-protect
	 (progn (modify-syntax-entry ?\. "_")
                (let ((,res (progn ,@code)))
                  (modify-syntax-entry ?\. ".")
                  ,res)))))

(defconst coq-generic-expression
  (mapcar (lambda (kw)
	    (list (capitalize kw)
; 		  (concat "\\<" kw "\\>" "\\s-+\\(\\w+\\)\\W" )
; da: that seems buggy (kw already in \\<,\\>; want symbols, not words)
		  (concat kw "\\s-+\\(\\_<\\(?:\\sw\\|\\s_\\)+\\_>\\)")
		  1))
	  (append coq-keywords-decl coq-keywords-defn coq-keywords-goal)))


;; Local Variables: ***
;; indent-tabs-mode: nil ***
;; End: ***

(provide 'coq-syntax)
;;; coq-syntax.el ends here
