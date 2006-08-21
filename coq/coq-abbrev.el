;; default abbrev table
; This is for coq V8, you should test coq version before loading

(require 'proof)

(defun holes-show-doc () 
  (interactive)
  (describe-variable 'holes-doc))

(defun coq-local-vars-list-show-doc ()
  (interactive)
  (describe-variable 'coq-local-vars-doc))


;;; We store all information on keywords (tactics or command) in big
;;; tables (ex: `coq-tactics-db') From there we get: menus including
;;; "smart" commands, completions for command coq-insert-... 
;;; and abbrev tables


;;; real value defined below
(defvar coq-tactics-db nil
  "The coq tactics information database.  This is a list of tactics
information lists. Each element is a list of the form 

(TAC-MENUNAME ABBREVIATION COMPLETION TO-COLORIZE INSERTION-FUN HIDE-IN-MENU)

TAC-MENUNAME is the name of tactic (or tactic variant) as it should
appear in menus.

ABBREVIATION is the abbreviation for completion via `expand-abbrev'.

COMPLETION is the complete text of the tactic, which may contain hole
denoted by \"#\" or \"@{}\".

If non-nil the optional TO-COLORIZE specifies the regexp to colorize
correponding to this tactic. ex: \"simple\\\\s-+destruct\"

If non-nil the optional INSERTION-FUN is the function to be called
when inserting the tactic. This allows to ask for more information to
assist tactic writing. This function is not called when using
completion, it is used when using menu or `coq-insert-tactic'.

If non-nil the optional HIDE-IN-MENU specifies that this tactic should
not appear in the menu but only in when calling `coq-insert-tactic'." )


;; Computes the max length of strings in a list
(defun max-length-db (l)
  (if (not l) 0
    (let ((lgth (length (car (car l))))
	  (lgthrest (max-length-db (cdr l))))
      (max lgth lgthrest))))


(defun coq-build-menu-from-db-internal (l size menuwidth)
  "Take a keyword database L and return insertion menus for them."
  (when (and l (> size 0))
    (let* ((hd (car l))(tl (cdr l))	; hd is a list of length 3 or 4
	   (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
	   (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
	   (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion 
	   (e4 (car-safe tl3)) (tl4 (cdr-safe tl3)) ; e4 = colorization string
	   (e5 (car-safe tl4))		; e5 = function for smart insertion
	   (e6 (car-safe (cdr-safe tl4))) ; e6 = if non-nil : hide in menu 
	   (entry-with (max (- menuwidth (length e1)) 0))
	   (spaces (make-string entry-with ? ))
	   (restofmenu (coq-build-menu-from-db-internal tl (- size 1) menuwidth)))

      (if (not e6)			; if not hidden
	  (cons 
	   (vector 
	    (concat e1
		    (if (not e2) ""
		      (concat spaces "("  e2
			      (substitute-command-keys " \\[expand-abbrev]") ")")))
	    (if e5 e5			; insertion function if present
	      `(holes-insert-and-expand ,e3)) ; otherwise insert completion
	    t)
	   restofmenu)
	restofmenu))))

(defun coq-build-title-menu (l size)
    (concat (car-safe (car-safe l))
	  " ... "
	  (car-safe (car-safe (nthcdr (- size 1) l)))))


(defun coq-build-menu-from-db (l &optional size)
  "Take a keyword database L and return a list of insertion menus for
 them.
Submenus contain SIZE entries (default 30)."
  (let ((lgth (length l)) (sz (or size 30)) (wdth (+ 2 (max-length-db coq-tactics-db))))
    (when l
      (if (<= lgth sz) 
	  (cons (cons (coq-build-title-menu l lgth)
		      (coq-build-menu-from-db-internal l lgth wdth)) nil)
	(cons (cons (coq-build-title-menu l sz)
		    (coq-build-menu-from-db-internal l sz wdth))
	      (coq-build-menu-from-db (nthcdr sz l) sz))))))


(defun coq-build-abbrev-table-from-db (l)
  (when l
    (let* ((hd (car l))(tl (cdr l))	; hd is a list of length 3 or 4
	   (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
	   (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
	   (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion 
	   )
      (if e2 (cons `(,e2 ,e3 holes-abbrev-complete) 
		   (coq-build-abbrev-table-from-db tl))
	(coq-build-abbrev-table-from-db tl)))))







(setq coq-tactics-db
  '(
    ("absurd " "abs" "absurd " "absurd")
    ("apply" "ap" "apply " "apply")
    ("assert by" "assb" "assert ( # : # ) by #" "assert")
    ("assert" "ass" "assert ( # : # )" "assert")
    ("assumption" "as" "assumption" "assumption")
    ("auto with arith" "awa" "auto with arith")
    ("auto with" "aw" "auto with @{db}")
    ("auto" "a" "auto" "auto")
    ("autorewrite with in using" "arwiu" "autorewrite with @{db,db...} in @{hyp} using @{tac}")
    ("autorewrite with in" "arwi" "autorewrite with @{db,db...} in @{hyp}")
    ("autorewrite with using" "arwu" "autorewrite with @{db,db...} using @{tac}")
    ("autorewrite with" "ar" "autorewrite with @{db,db...}" "autorewrite")
    ("cases" "c" "cases " "cases")
    ("cbv" "cbv" "cbv beta [#] delta iota zeta" "cbv")
    ("change in" "chi" "change # in #")
    ("change with in" "chwi" "change # with # in #")
    ("change with" "chw" "change # with")
    ("change" "ch" "change " "change")
    ("clear" "cl" "clear" "clear")
    ("clearbody" "cl" "clearbody" "clearbody")
    ("cofix" "cof" "cofix" "cofix")
    ("coinduction" "coind" "coinduction" "coinduction")
    ("compare" "cmpa" "compare # #" "compare")
    ("compute" "cmpu" "compute" "compute")
    ("congruence" "cong" "congruence" "congruence")
    ("constructor" "cons" "constructor" "constructor")
    ("contradiction" "contr" "contradiction" "contradiction")
    ("cut" "cut" "cut" "cut")
    ("cutrewrite" "cutr" "cutrewrite -> # = #" "cutrewrite")
    ("decide equality" "deg" "decide equality" "decide\\-+equality")
    ("decompose" "dec" "decompose [#] #" "decompose")
    ("decompose record" "decr" "decompose record #" "decompose\\s-+record")
    ("decompose sum" "decs" "decompose sum #" "decompose\\-+sum")
    ("dependent inversion" "depinv" "dependent inversion" "dependent\\s-+inversion")
    ("dependent inversion with" "depinvw" "dependent inversion # with #")
    ("dependent inversion_clear" "depinvc" "dependent inversion_clear" "dependent\\s-+inversion_clear")
    ("dependent inversion_clear with" "depinvw" "dependent inversion_clear # with #")
    ("dependent rewrite ->" "depr" "dependent rewrite -> @{id}" "dependent\\s-+rewrite")
    ("dependent rewrite <-" "depr<" "dependent rewrite <- @{id}")
    ("destruct as" "desa" "destruct # as #")
    ("destruct using" "desu" "destruct # using #")
    ("destruct" "des" "destruct "  "destruct")
    ("discriminate" "dis" "discriminate" "discriminate")
    ("discrR" "discrR" "discrR" "discrR")
    ("double induction" "dind" "double induction # #" "double\\s-+induction")
    ("eapply" "eap" "eapply #" "eapply")
    ("eauto with arith" "eawa" "eauto with arith")
    ("eauto with" "eaw" "eauto with @{db}")
    ("eauto" "ea" "eauto" "eauto")
    ("econstructor" "econs" "econstructor" "econstructor")
    ("eexists" "eex" "eexists" "eexists")
    ("eleft" "eleft" "eleft" "eleft")
    ("elim using" "elu" "elim # using #")
    ("elim" "e" "elim #" "elim")
    ("elimtype" "elt" "elimtype" "elimtype")
    ("eright" "erig" "eright" "eright")
    ("esplit" "esp" "esplit" "esplit")
    ("exact" "exa" "exact" "exact")
    ("exists" "ex" "exists #" "exists")
    ("fail" "fail" "fail" "fail")
    ("field" "field" "field" "field")
    ("firstorder" "fsto" "firstorder" "firstorder")
    ("firstorder with" "fsto" "firstorder with #")
    ("firstorder with using" "fsto" "firstorder # with #")
    ("fold" "fold" "fold #" "fold")
    ("fourier" "four" "fourier" "fourier")
    ("functional induction" "fi" "functional induction @{f} @{args}" "functional\\s-+induction")
    ("generalize" "g" "generalize #" "generalize")
    ("generalize dependent" "gd" "generalize dependent #" "generalize\\s-+dependent")
    ("hnf" "hnf" "hnf" "hnf")
    ("induction" "ind" "induction #" "induction")
    ("induction using" "indu" "induction # using #")
    ("injection" "inj" "injection #" "injection")
    ("instantiate" "inst" "instantiate" "instantiate")
    ("intro" "i" "intro" "intro")
    ("intro after" "ia" "intro # after #")
    ("intros" "is" "intros #" "intros")
    ("intros! (guess names)" nil "intros #" nil coq-insert-intros)
    ("intros until" "isu" "intros until #")
    ("intuition" "intu" "intuition #" "intuition")
    ("inversion" "inv" "inversion #" "inversion")
    ("inversion in" "invi" "inversion # in #")
    ("inversion using" "invu" "inversion # using #")
    ("inversion using in" "invui" "inversion # using # in #")
    ("inversion_clear" "invcl" "inversion_clear" "inversion_clear")
;    ("jp")
    ("lapply" "lap" "lapply" "lapply")
    ("lazy" "lazy" "lazy beta [#] delta iota zeta" "lazy")
    ("left" "left" "left" "left")
;    ("lettac" "" "lettac" "lettac")
    ("linear" "lin" "linear" "linear")
    ("load" "load" "load" "load")
    ("move after" "mov" "move # after #" "move")
    ("omega" "o" "omega" "omega")
    ("pattern" "pat" "pattern" "pattern")
    ("pattern(s)" "pats" "pattern # , #")
    ("pattern at" "pata" "pattern # at #")
    ("pose" "po" "pose ( # := # )" "pose")
    ("prolog" "prol" "prolog" "prolog")
    ("quote" "quote" "quote" "quote")
    ("quote []" "quote2" "quote # [#]")
    ("red" "red" "red" "red")
    ("refine" "ref" "refine" "refine")
    ("reflexivity" "refl" "reflexivity #" "reflexivity")
    ("rename into" "ren" "rename # into #" "rename")
    ("replace with" "rep" "replace # with #")
    ("replace with in" "repi" "replace # with # in #")
    ("rewrite <- in" "ri<" "rewrite <- # in #")
    ("rewrite <-" "r<" "rewrite <- #")
    ("rewrite in" "ri" "rewrite # in #")
    ("rewrite" "r" "rewrite #" "rewrite")
    ("right" "rig" "right" "right")
    ("ring" "ring" "ring #" "ring")
    ("set in * |-" "seth" "set ( # := #) in * |-")
    ("set in *" "set*" "set ( # := #) in *")
    ("set in |- *" "setg" "set ( # := #) in |- *")
    ("set in" "seti" "set ( # := #) in #")
    ("set" "set" "set ( # := #)" "set")
    ("setoid_replace with" "strep" "setoid_replace # with #" "setoid_replace")
    ("simpl" "s" "simpl" "simpl")
    ("simpl" "sa" "simpl # at #")
    ("simple destruct" "sdes" "simple destruct" "simple\\s-+destruct")
    ("simple inversion" "sinv" "simple inversion" "simple\\s-+inversion")
    ("simple induction" "sind" "simple induction" "simple\\s-+induction")
    ("simplify_eq" "simeq" "simplify_eq @{hyp}" "simplify_eq")
    ("specialize" "spec" "specialize" "specialize")
    ("split" "sp" "split" "split")
    ("split_Rabs" "spra" "splitRabs" "split_Rabs")
    ("split_Rmult" "sprm" "splitRmult" "split_Rmult")
    ("stepl" "stl" "stepl #" "stepl")
    ("stepl by" "stlb" "stepl # by #")
    ("stepr" "str" "stepr #" "stepr")
    ("stepr by" "strb" "stepr # by #")
    ("subst" "su" "subst #" "subst")
    ("symmetry" "sy" "symmetry" "symmetry")
    ("symmetry in" "sy" "symmetry in #")
    ("tauto" "ta" "tauto" "tauto")
    ("transitivity" "trans" "transitivity #" "transitivity")
    ("trivial" "t" "trivial" "trivial")
    ("trivial with" "t" "trivial with @{db}")
    ("unfold" "u" "unfold #" "unfold")
    ("unfold(s)" "us" "unfold # , #")
    ("unfold in" "unfi" "unfold # in #")
    ("unfold at" "unfa" "unfold # at #")
    )
  )


(defconst coq-tactics-menu 
  (append '("INSERT TACTICS" 
	    ["Intros (smart)" coq-insert-intros t])
	  (coq-build-menu-from-db coq-tactics-db)))

(defconst coq-tactics-abbrev-table 
  (coq-build-abbrev-table-from-db coq-tactics-db))



(defvar coq-commands-db
  '(
    ("Arguments Scope" "argsc" "Arguments Scope @{id} [ @{_} ]" "Arguments\\s-+Scope")
    ("Bind Scope" "bndsc" "Bind Scope @{scope} with @{type}" "Bind\\s-+Scope")
    ("Close Local Scope" "cllsc" "Close Local Scope #" "Close\\s-+Local\\s-+Scope")
    ("Close Scope" "clsc" "Close Scope #" "Close\\s-+Scope")
    ("Coercion" "coerc" "Coercion @{id} : @{typ1} >-> @{typ2}." "Coercion")
    ("Declare Module : :=" "dm" "Declare Module # : # := #." "Declare\\s-+Module")
    ("Declare Module :" "dmi" "Declare Module # : #.\n#\nEnd #.")
    ("Declare Module <: :=" "dm2" "Declare Module # <: # := #.")
    ("Declare Module <:" "dmi2" "Declare Module # <: #.\n#\nEnd #.")
    ("Definition (2 args)" "def2" "Definition # (# : #) (# : #):# := #.")
    ("Definition (3 args)" "def3" "Definition # (# : #) (# : #) (# : #):# := #.")
    ("Definition (4 args)" "def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #.")
    ("Definition" "def" "Definition #:# := #." "Definition")
    ("Delimit Scope" "delsc" "Delimit Scope @{scope} with @{id}" "Delimit\\s-+Scope" )
    ("Fixpoint" "fix" "Fixpoint # (#:#) {struct @{arg}} : # :=\n#." "Fixpoint")
    ("Fixpoint measure" "fix" "Fixpoint # (#:#) {Measure @{f} @{arg}} : # :=\n#.")
    ("Fixpoint wf" "fix" "Fixpoint # (#:#) {struct @{R} @{arg}} : # :=\n#." )
    ("Functional Scheme" "fs" "Functional Scheme @{name} := Induction for @{fun}." "Functional\\s-+Scheme")
    ("Functional Scheme with" "fsw" "Functional Scheme @{name} := Induction for @{fun} with @{mutfuns}." )
    ("Hint Constructors" "hc" "Hint Constructors # : #." "Hint\\s-+Constructors")
    ("Hint Extern" "he" "Hint Extern @{cost} @{pat} => @{tac} : @{db}." "Hint\\s-+Extern")
    ("Hint Immediate" "hi" "Hint Immediate # : @{db}." "Hint\\s-+Immediate")
    ("Hint Resolve" "hr" "Hint Resolve # : @{db}." "Hint\\s-+Resolve")
    ("Hint Rewrite ->" "hrw" "Hint Rewrite -> @{t1,t2...} using @{tac} : @{db}." "Hint\\s-+Rewrite")
    ("Hint Rewrite <-" "hrw" "Hint Rewrite <- @{t1,t2...} using @{tac} : @{db}." )
    ("Hint Unfold" "hu" "Hint Unfold # : #." "Hint\\s-+Unfold")
    ("Inductive" "indv" "Inductive # : # := # : #." "Inductive")
    ("Inductive (2 args)" "indv2" "Inductive # : # :=\n| # : #\n| # : #." )
    ("Inductive (3 args)" "indv3" "Inductive # : # :=\n| # : #\n| # : #\n| # : #." )
    ("Inductive (4 args)" "indv4" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #." )
    ("Inductive (5 args)" "indv5" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #\n| # : #." )
    ("Infix" "inf" "Infix \"#\" := # (at level #) : @{scope}." "Infix")
    ("Lemma" "l" "Lemma # : #." "Lemma")
    ("Module! (interactive)" nil "Module # : #.\n#\nEnd #." nil coq-insert-section-or-module)
    ("Module :" "moi" "Module # : #.\n#\nEnd #." "Module")
    ("Module :=" "mo" "Module # : # := #." )
    ("Module <: :=" "mo2" "Module # <: # := #." )
    ("Module <:" "moi2" "Module # <: #.\n#\nEnd #." )
    ("Module Type" "mti" "Module Type #.\n#\nEnd #." "Module\\s-+Type")
    ("Notation (assoc)" "notas" "Notation \"#\" := # (at level #, # associativity)." )
    ("Notation (at assoc)" "notassc" "Notation \"#\" := # (at level #, # associativity) : @{scope}." )
    ("Notation (at at scope)" "notasc" "Notation \"#\" := # (at level #, # at level #) : @{scope}." )
    ("Notation (at at)" "nota" "Notation \"#\" := # (at level #, # at level #)." )
    ("Notation (only parsing)" "notsp" "Notation # := # (only parsing)." )
    ("Notation (simple)" "nots" "Notation # := #." "Notation")
    ("Notation Local (only parsing)" "notslp" "Notation Local # := # (only parsing)." )
    ("Notation Local" "notsl" "Notation Local # := #." "Notation\\s-+Local")
    ("Open Local Scope" "oplsc" "Open Local Scope #" "Open\\s-+Local\\s-+Scope")
    ("Open Scope" "opsc" "Open Scope #" "Open\\s-+Scope")
    ("Print" "p" "Print #" "Print")
    ("Scheme Induction" "sc" "Scheme @{name} := Induction for # Sort #.""Scheme")
    ("Set Printing All" "sprall" "Set Printing All" "Set\\s-+Printing\\s-+All")
    ("Set Printing Notations" "sprn" "Set Printing Notations" "Set\\s-+Printing\\s-+Notations")
    ("Unset Printing All" "unsprall" "Unset Printing All" "Unset\\s-+Printing\\s-+All")
    ("Unset Printing Notations" "unsprn" "Unset Printing Notations" "Unset\\s-+Printing\\s-+Notations")
    ("Variable" "v" "Variable # : #." "Variable")
    ("Variables" "vs" "Variables # , # : #." "Variables")
    ("print" "pr" "print #" "print")
    ))

(defconst coq-commands-menu 
  (append '("INSERT COMMAND" 
	    ["Module/Section (smart)" coq-insert-section-or-module t]
	    ["Require (smart)" coq-insert-requires t])
	  (coq-build-menu-from-db coq-commands-db)))

(defconst coq-commands-abbrev-table 
  (coq-build-abbrev-table-from-db coq-commands-db))


(defvar coq-terms-db
  '(
    ("fun (1 args)" "f" "fun #:# => #" "fun")
    ("fun (2 args)" "f2" "fun (#:#) (#:#) => #")
    ("fun (3 args)" "f3" "fun (#:#) (#:#) (#:#) => #")
    ("fun (4 args)" "f4" "fun (#:#) (#:#) (#:#) (#:#) => #" )
    ("forall" "fo" "forall #:#,#" "forall")
    ("forall (2 args)" "fo2" "forall (#:#) (#:#), #" )
    ("forall (3 args)" "fo3" "forall (#:#) (#:#) (#:#), #" )
    ("forall (4 args)" "fo4" "forall (#:#) (#:#) (#:#) (#:#), #" )
    ("if" "if" "if # then # else #" "if")
    ("let in" "li" "let # := # in #" "let")
    ("match! (from type)" nil "" "match" coq-insert-match)
    ("match with" "m" "match # with\n| # => #\nend")
    ("match with 2" "m2" "match # with\n| # => #\n| # => #\nend" )
    ("match with 3" "m3" "match # with\n| # => #\n| # => #\n| # => #\nend" )
    ("match with 4" "m4" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\nend" )
    ("match with 5" "m5" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\n| # => #\nend" )
    ))


(defconst coq-terms-menu 
  (append '("INSERT TERM" 
	    ["Match!" coq-insert-match t])
	  (coq-build-menu-from-db coq-terms-db)))

(defconst coq-terms-abbrev-table 
  (coq-build-abbrev-table-from-db coq-terms-db))



;#s and @{..} are replaced by holes by holes-abbrev-complete
(if (boundp 'holes-abbrev-complete)
	 ()
  (define-abbrev-table 'coq-mode-abbrev-table
    coq-tactics-abbrev-table))

(when t (setq dummy
      '(
		("a" "auto" holes-abbrev-complete 4)
		("ar" "autorewrite with @{db,db...} using @{tac}" holes-abbrev-complete 1)
		("ab" "absurd " holes-abbrev-complete 0)
		("abs" "absurd " holes-abbrev-complete 0)
		("ap" "apply " holes-abbrev-complete 16)
		("argsc" "Arguments Scope @{id} [ @{_} ]" holes-abbrev-complete 4)
		("as" "assumption" holes-abbrev-complete 4)
		("ass" "assert ( # : # )" holes-abbrev-complete 4)
		("au" "auto" holes-abbrev-complete 1)
		("aw" "auto with " holes-abbrev-complete 1)
		("awa" "auto with arith" holes-abbrev-complete 4)
		("c" "cases " holes-abbrev-complete 1)
		("cbv" "cbv beta delta iota zeta" holes-abbrev-complete 0)
		("bndsc" "Bind Scope @{scope} with @{type}" holes-abbrev-complete 1)
		("ch" "change " holes-abbrev-complete 1)
		("chi" "change # in #" holes-abbrev-complete 1)
		("chwi" "change # with # in #" holes-abbrev-complete 1)
		("cllsc" "Close Local Scope #" holes-abbrev-complete 0)
		("clsc" "Close Scope #" holes-abbrev-complete 0)
		("coerc" "Coercion @{id} : @{typ1} >-> @{typ2}." holes-abbrev-complete 3)
		("con" "constructor" holes-abbrev-complete 3)
		("cong" "congruence" holes-abbrev-complete 3)
		("dec" "decompose [#] @{hyp}" holes-abbrev-complete 3)
		("def" "Definition #:# := #." holes-abbrev-complete 5)
		("def2" "Definition # (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def3" "Definition # (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("deg" "decide equality" holes-abbrev-complete 3)
		("delsc" "Delimit Scope @{scope} with @{id}" holes-abbrev-complete 3) 
		("des" "destruct " holes-abbrev-complete 0)
		("desu" "destruct # using #" holes-abbrev-complete 0)
		("desa" "destruct # as #" holes-abbrev-complete 0)
		("dis" "discriminate" holes-abbrev-complete 0)
		("dm" "Declare Module # : # := #." holes-abbrev-complete 0)
		("dm2" "Declare Module # <: # := #." holes-abbrev-complete 0)
		("dmi" "Declare Module # : #.\n#\nEnd #." holes-abbrev-complete 0)
		("dmi2" "Declare Module # <: #.\n#\nEnd #." holes-abbrev-complete 0)
		("e" "elim #" holes-abbrev-complete 1)
		("ea" "eauto" holes-abbrev-complete 0)
		("eap" "eapply #" holes-abbrev-complete 0)
		("eaw" "eauto with @{db}" holes-abbrev-complete 0)
		("eawa" "eauto with arith" holes-abbrev-complete 0)
		("el" "elim #" holes-abbrev-complete 0)
		("elu" "elim # using #" holes-abbrev-complete 0)
		("ex" "exists #" holes-abbrev-complete 0)
		("f" "fun # => #" holes-abbrev-complete 0)
		("f1" "fun #:# => #" holes-abbrev-complete 0)
		("f2" "fun (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f3" "fun (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f4" "fun (#:#) (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("fi" "functional induction @{f} @{args}" holes-abbrev-complete 0)
		("fix" "Fixpoint # (#:#) {struct @{arg}} : # :=\n#." holes-abbrev-complete 3)
		("fo" "forall #,#" holes-abbrev-complete 0)
		("fo1" "forall #:#,#" holes-abbrev-complete 0)
		("fo2" "forall (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo3" "forall (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo4" "forall (#:#) (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("fs" "Functional Scheme @{name} := Induction for @{fun}." holes-abbrev-complete 0)
		("fsto" "firstorder" holes-abbrev-complete 0)
		("fsw" "Functional Scheme @{name} := Induction for @{fun} with @{mutfuns}." holes-abbrev-complete 0)
		("g" "generalize #" holes-abbrev-complete 0)
		("ge" "generalize #" holes-abbrev-complete 0)
		("gen" "generalize #" holes-abbrev-complete 0)
		("hc" "Hint Constructors # : #." holes-abbrev-complete 0)
		("he" "Hint Extern @{cost} @{pat} => @{tac} : @{db}." holes-abbrev-complete 0)
		("hi" "Hint Immediate # : @{db}." holes-abbrev-complete 0)
		("hr" "Hint Resolve # : @{db}." holes-abbrev-complete 0)
		("hrw" "Hint Rewrite -> @{t1,t2...} using @{tac} : @{db}." holes-abbrev-complete 0)
		("hs" "Hints # : #." holes-abbrev-complete 0)
		("hu" "Hint Unfold # : #." holes-abbrev-complete 0)
		("i" "intro " holes-abbrev-complete 10)
		("if" "if # then # else #" holes-abbrev-complete 1)
		("in" "intro" holes-abbrev-complete 1)
		("inf" "Infix \"#\" := # (at level #) : @{scope}." holes-abbrev-complete 1)
		("ind" "induction #" holes-abbrev-complete 2)
		("indv" "Inductive # : # := # : #." holes-abbrev-complete 0)
		("indv2" "Inductive # : # :=\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv3" "Inductive # : # :=\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv4" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv5" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("inj" "injection #" holes-abbrev-complete 2)
		("inv" "inversion #" holes-abbrev-complete 9)
		("intu" "intuition #" holes-abbrev-complete 9)
		("is" "intros #" holes-abbrev-complete 11)
		("ite" "if # then # else #" holes-abbrev-complete 1)
		("l" "Lemma # : #." holes-abbrev-complete 4)
		("li" "let # := # in #" holes-abbrev-complete 1)
		("m" "match # with\n| # => #\nend" holes-abbrev-complete 1)
		("m2" "match # with\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("m3" "match # with\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("m4" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("m5" "match # with\n| # => #\n| # => #\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("mt" "Module Type # := #." holes-abbrev-complete 0)
		("mti" "Module Type #.\n#\nEnd #." holes-abbrev-complete 0)
		("mo" "Module # : # := #." holes-abbrev-complete 0)
		("mo2" "Module # <: # := #." holes-abbrev-complete 0)
		("moi" "Module # : #.\n#\nEnd #." holes-abbrev-complete 0)
		("moi2" "Module # <: #.\n#\nEnd #." holes-abbrev-complete 0)
		("nots" "Notation # := #." holes-abbrev-complete 0)
		("notsp" "Notation # := # (only parsing)." holes-abbrev-complete 0)
		("notsl" "Notation Local # := #." holes-abbrev-complete 0)
		("notslp" "Notation Local # := # (only parsing)." holes-abbrev-complete 0)
		("not" "Notation \"#\" := # (at level #, # at level #)." holes-abbrev-complete 0)
		("nota" "Notation \"#\" := # (at level #, # at level #)." holes-abbrev-complete 0)
		("notas" "Notation \"#\" := # (at level #, # associativity)." holes-abbrev-complete 0)
		("notasc" "Notation \"#\" := # (at level #, # at level #) : @{scope}." holes-abbrev-complete 0)
		("notassc" "Notation \"#\" := # (at level #, # associativity) : @{scope}." holes-abbrev-complete 0)
		("o" "omega" holes-abbrev-complete 0)
		("om" "omega" holes-abbrev-complete 0)
		("oplsc" "Open Local Scope #" holes-abbrev-complete 0)
		("opsc" "Open Scope #" holes-abbrev-complete 0)
		("p" "Print #" holes-abbrev-complete 3)
		("po" "pose ( # := # )" nil 0)
		("pr" "print #" holes-abbrev-complete 2)
		("rep" "replace # with #" holes-abbrev-complete 19)
		("r" "rewrite #" holes-abbrev-complete 19)
		("r<" "rewrite <- #" holes-abbrev-complete 0)
		("rl" "rewrite <- #" holes-abbrev-complete 0)
		("refl" "reflexivity #" holes-abbrev-complete 0)
		("ri" "rewrite # in #" holes-abbrev-complete 19)
		("ril" "rewrite <- # in #" holes-abbrev-complete 0)
		("ri<" "rewrite <- # in #" holes-abbrev-complete 0)
		("re" "rewrite #" holes-abbrev-complete 0)
		("re<" "rewrite <- #" holes-abbrev-complete 0)
		("ring" "ring #" holes-abbrev-complete 19)
		("s" "simpl" holes-abbrev-complete 23)
		("set" "set ( # := #)" holes-abbrev-complete 23)
		("seth" "set ( # := #) in * |-" holes-abbrev-complete 23)
		("setg" "set ( # := #) in |- *" holes-abbrev-complete 23)
		("seti" "set ( # := #) in #" holes-abbrev-complete 23)
		("su" "subst #" holes-abbrev-complete 23)
		("sc" "Scheme @{name} := Induction for # Sort #." nil 0)
		("si" "simpl" holes-abbrev-complete 0)
		("sp" "Split" holes-abbrev-complete 1)
		("sy" "symmetry" holes-abbrev-complete 0)
		("sym" "symmetry" holes-abbrev-complete 0)
		("sprall" "Set Printing All" holes-abbrev-complete 1)
		("unsprall" "Unset Printing All" holes-abbrev-complete 1)
		("sprn" "Set Printing Notations" holes-abbrev-complete 1)
		("unsprn" "Unset Printing Notations" holes-abbrev-complete 1)
		("t" "trivial" holes-abbrev-complete 1)
		("tr" "trivial" holes-abbrev-complete 1)
		("trans" "transitivity #" holes-abbrev-complete 1)
		("ta" "tauto" holes-abbrev-complete 1)
		("u" "unfold #" holes-abbrev-complete 1)
		("un" "unfold #" holes-abbrev-complete 7)
		("v" "Variable # : #." holes-abbrev-complete 7)
		("vs" "Variables # : #." holes-abbrev-complete 7)
		)
	 )
  )

;TODO: build the command submenu automatically from abbrev table
(defpgdefault menu-entries 
;  (append
;   coq-tactics-menu
   `(
     ["Print..." coq-Print t]
     ["Check..." coq-Check t]
     ["About..." coq-About t]
     ("OTHER QUERIES"
      ["Print Hint" coq-PrintHint t]
      ["Show ith goal..." coq-Show t]
      ["Show Tree" coq-show-tree t]
      ["Show Proof" coq-show-proof t]
      ["Show Conjectures" coq-show-conjectures t];; maybe not so useful with editing in PG?
      ""
      ["Print..." coq-Print t]
      ["Check..." coq-Check t]
      ["About..." coq-About t]
      ["Search isos/pattern..." coq-SearchIsos t]
      ["Locate constant..." coq-LocateConstant t]
      ["Locate Library..." coq-LocateLibrary t]
      ""
      ["Locate notation..." coq-LocateNotation t]
      ["Print Implicit..." coq-Print t]
      ["Print Scope/Visibility..." coq-PrintScope t]
      )

     ["insert command (interactive)" coq-insert-command t]
     ,coq-commands-menu

     
     ["insert term (interactive)" coq-insert-term t]
     ,coq-terms-menu


     ["insert tactic (interactive)" coq-insert-tactic t]
     ,coq-tactics-menu

     ;; da: I added Show sub menu, not sure if it's helpful, but why not.
     ;; FIXME: submenus should be split off here.  Also, these commands
     ;; should only be available when a proof is open.

     ("Holes" 
      ;; da: I tidied this menu a bit.  I personally think this "trick"
      ;; of inserting strings to add documentation looks like a real
      ;; mess in menus ... I've removed it for the three below since 
      ;; the docs below appear in popup in messages anyway.
      ;; 
      ;; "Make a hole active   click on it"
      ;; "Disable a hole   click on it (button 2)"
      ;; "Destroy a hole   click on it (button 3)"
      ["Make hole at point"  holes-set-make-active-hole t]
      ["Make selection a hole"  holes-set-make-active-hole t]
      ["Replace active hole by selection"  holes-replace-update-active-hole t]
      ["Jump to active hole"  holes-set-point-next-hole-destroy t]
      ["Forget all holes in buffer"  holes-clear-all-buffer-holes t]
      ["Tell me about holes?" holes-show-doc t]
      ;; look a bit better at the bottom
      "Make hole with mouse: C-M-select"
      "Replace hole with mouse: C-M-Shift select";; da: does this one work??
      )

     ;; da: I also added abbrev submenu.  Surprising Emacs doesn't have one?
     ("Abbrevs"
      ["Expand at point" expand-abbrev t]
      ["Unexpand last" unexpand-abbrev t]
      ["List abbrevs" list-abbrevs t]
      ["Edit abbrevs" edit-abbrevs t];; da: is it OK to add edit?
      ["Abbrev mode" abbrev-mode 
       :style toggle
       :selected (and (boundp 'abbrev-mode) abbrev-mode)])
     ;; With all these submenus you have to wonder if these things belong
     ;; on the main menu.  Are they the most often used?
     ["Compile" coq-Compile t]
     ["Set coq prog name *for this file persistently*" coq-ask-insert-coq-prog-name t]
     ["help on setting prog name persistently for a file" coq-local-vars-list-show-doc t]
     ))
;)

;; da: Moved this from the main menu to the Help submenu.  
;; It also appears under Holes, anyway.
(defpgdefault help-menu-entries
  '(["Tell me about holes?" holes-show-doc t]))


(provide 'coq-abbrev)

