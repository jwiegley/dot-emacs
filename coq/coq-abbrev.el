;; default abbrev table
; This is for coq V8, you should test coq version before loading

(defun holes-show-doc () 
  (interactive)
  (describe-variable 'holes-doc))

;#s and @{..} are replaced by holes by holes-abbrev-complete
(if (boundp 'holes-abbrev-complete)
	 ()
  (define-abbrev-table 'coq-mode-abbrev-table
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
		("setg" "set ( # := #) in |-*" holes-abbrev-complete 23)
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
  '(
    ["Print..." coq-Print t]
    ["Check..." coq-Check t]
    ["About..." coq-About t]
    ("OTHER QUERIES"
     ["Print Hint" coq-PrintHint t]
     ["Show ith goal..." coq-Show t]
     ["Show Tree" coq-show-tree t]
     ["Show Proof" coq-show-proof t]
     ["Show Conjectures" coq-show-conjectures t] ;; maybe not so useful with editing in PG?
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
    ["Smart intros" coq-intros t]
    ["Require/Export/Import" coq-insert-requires t]
    ("INSERT COMMAND" 
      "COMMAND               ABBREVIATION"
     ["Definition            def<C-BS>" (holes-insert-and-expand "def") t]
     ["Fixpoint              fix<C-BS>" (holes-insert-and-expand "fix") t]
     ["Lemma                 l<C-BS>" (holes-insert-and-expand "l") t]
     ""
     ["Inductive             indv<C-BS>" (holes-insert-and-expand "indv") t]
     ["Inductive1            indv1<C-BS>" (holes-insert-and-expand "indv1") t]
     ["Inductive2             indv2<C-BS>" (holes-insert-and-expand "indv2") t]
     ["Inductive3            indv3<C-BS>" (holes-insert-and-expand "indv3") t]
     ["Inductive4            indv4<C-BS>" (holes-insert-and-expand "indv4") t]
     ""
     ["Section/Module (interactive)..." coq-insert-section-or-module t]
     ["Require/Export/Import" coq-insert-requires t]
     ""
     ("Modules"
      "COMMAND               ABBREVIATION"
      ["Module (interactive)... " coq-insert-section-or-module t]
      ["Module                mo<C-BS>" (holes-insert-and-expand "mo") t]
      ["Module (<:)           mo2<C-BS>" (holes-insert-and-expand "mo") t]
;      ["Module (interactive)  moi<C-BS>" (holes-insert-and-expand "moi") t]
;      ["Module (interactive <:) moi2<C-BS>" (holes-insert-and-expand "moi2") t]
      ["Module Type           mt<C-BS>" (holes-insert-and-expand "mt") t]
;      ["Module Type (interactive) mti<C-BS>" (holes-insert-and-expand "mti") t]
;      ""
      ["Declare Module        dm<C-BS>" (holes-insert-and-expand "dm") t]
      ["Declare Module (<:)   dm2<C-BS>" (holes-insert-and-expand "dm") t]
;      ["Declare Module (inter.) dmi<C-BS>" (holes-insert-and-expand "dmi") t]
;      ["Declare Module (inter. <:) dmi2<C-BS>" (holes-insert-and-expand "dmi2") t]
      )
     ("Hints"
      "COMMAND               ABBREVIATION"
      ["Hint Constructors     hc<C-BS>" (holes-insert-and-expand "hc") t]
      ["Hint Immediate        hi<C-BS>" (holes-insert-and-expand "hi") t]
      ["Hint Resolve          hr<C-BS>" (holes-insert-and-expand "hr") t]
      ["Hint Rewrite          hrw<C-BS>" (holes-insert-and-expand "hrw") t]
      ["Hint Extern           he<C-BS>" (holes-insert-and-expand "he") t]
     )
     ("Schemes"
      "COMMAND               ABBREVIATION"
      ["Scheme                 sc<C-BS>" (holes-insert-and-expand "sc") t]
      ["Functional Scheme      fs<C-BS>" (holes-insert-and-expand "fs") t]
      ["Functional Scheme with fsw<C-BS>" (holes-insert-and-expand "fsw") t]
      )
     ("Notations"
      "COMMAND               ABBREVIATION"
      ""
      ["Open Scope                opsc<C-BS>" (holes-insert-and-expand "opsc") t]     
      ["Open Local Scope          oplsc<C-BS>" (holes-insert-and-expand "oplsc") t]     
      ["Close Scope               clsc<C-BS>" (holes-insert-and-expand "clsc") t]     
      ["Open Local Scope          cllsc<C-BS>" (holes-insert-and-expand "cllsc") t]     
      ""
      ["Set Printing Notations     sprn<C-BS>" (holes-insert-and-expand "sprn") t]
      ["Unset Printing Notations   unsprn<C-BS>" (holes-insert-and-expand "unsprn") t]
      ["Set Printing All           sprall<C-BS>" (holes-insert-and-expand "sprall") t]
      ["Unset Printing All         unsprall<C-BS>" (holes-insert-and-expand "unsprall") t]
      ""
      ["Print Scope/Visibility..." coq-PrintScope t]
      ["Locate..." coq-LocateNotation t]

      ""
      ["Infix                      inf<C-BS>" (holes-insert-and-expand "inf") t]     
      ["Notation (simple)          nots<C-BS>" (holes-insert-and-expand "nots") t]     
      ["Notation (simple,only parsing) notsp<C-BS>" (holes-insert-and-expand "notsp") t]
      ["Notation (simple,local)    notsl<C-BS>" (holes-insert-and-expand "notsl") t]     
      ["Notation (simple,local,only parsing) notslp<C-BS>" (holes-insert-and-expand "notslp") t]
      ""
      ["Notation (no assoc)        nota<C-BS>" (holes-insert-and-expand "nota") t]     
      ["Notation (assoc)           notas<C-BS>" (holes-insert-and-expand "notas") t] 
      ["Notation (no assoc, scope) notasc<C-BS>" (holes-insert-and-expand "notasc") t] 
      ["Notation (assoc, scope)    notassc<C-BS>" (holes-insert-and-expand "notassc") t]
      ["Delimit Scope              delsc<C-BS>" (holes-insert-and-expand "delsc") t]
      ["Arguments Scope            argsc<C-BS>" (holes-insert-and-expand "argsc") t]
      ["Bind Scope                 bndsc<C-BS>" (holes-insert-and-expand "bndsc") t]
      )
     ""
     ["Coercion          coerc<C-BS>" (holes-insert-and-expand "coerc") t]
     )

    ("INSERT TERM" 
     "FORM           ABBREVIATION"
     ["forall        fo<C-BS>"  (holes-insert-and-expand "fo") t]
     ["forall1       fo1<C-BS>"  (holes-insert-and-expand "fo1") t]
     ["forall2       fo2<C-BS>" (holes-insert-and-expand "fo2") t]
     ["forall3       fo3<C-BS>" (holes-insert-and-expand "fo3") t]
     ["forall4       fo4<C-BS>" (holes-insert-and-expand "fo4") t]
     ""
     ["fun           f<ctrl-bacspace>"  (holes-insert-and-expand "f") t]
     ["fun1          f1<ctrl-bacspace>"  (holes-insert-and-expand "f1") t]
     ["fun2          f2<C-BS>" (holes-insert-and-expand "f2") t]
     ["fun3          f3<C-BS>" (holes-insert-and-expand "f3") t]
     ["fun4          f4<C-BS>" (holes-insert-and-expand "f4") t]
     ""
     ["if then else  if<C-BS>"  (holes-insert-and-expand "if") t]
     ["let in        li<C-BS>"  (holes-insert-and-expand "li") t]
     ""
     ["match (smart)        "  coq-match t]
     ["match         m<C-BS>"  (holes-insert-and-expand "m") t]
     ["match2        m2<C-BS>"  (holes-insert-and-expand "m2") t]
     ["match3        m3<C-BS>"  (holes-insert-and-expand "m3") t]
     ["match4        m4<C-BS>"  (holes-insert-and-expand "m4") t]
     )

    ("INSERT TACTIC (a-f)" 
     "TACTIC           ABBREVIATION"
     ["absurd                 abs<C-BS>"  (holes-insert-and-expand "abs") t]
     ["assumption              as<C-BS>"  (holes-insert-and-expand "as") t]
     ["assert                 ass<C-BS>"  (holes-insert-and-expand "ass") t]
     ["auto                     a<C-BS>"  (holes-insert-and-expand "a") t]
     ["auto with               aw<C-BS>"  (holes-insert-and-expand "aw") t]
     ["auto with arith        awa<C-BS>"  (holes-insert-and-expand "awa") t]
     ["autorewrite             ar<C-BS>"  (holes-insert-and-expand "ar") t]
     ["cases                    c<C-BS>"  (holes-insert-and-expand "c") t]
     ["change                  ch<C-BS>"  (holes-insert-and-expand "ch") t]
     ["change in              chi<C-BS>"  (holes-insert-and-expand "chi") t]
     ["change with in        chwi<C-BS>"  (holes-insert-and-expand "chwi") t]
     ["constructor            con<C-BS>"  (holes-insert-and-expand "con") t]
     ["congruence            cong<C-BS>"  (holes-insert-and-expand "cong") t]
     ["decompose              dec<C-BS>"  (holes-insert-and-expand "dec") t]
     ["decide equality        deg<C-BS>"  (holes-insert-and-expand "deg") t]
     ["destruct               des<C-BS>"  (holes-insert-and-expand "des") t]
     ["destruct using        desu<C-BS>"  (holes-insert-and-expand "desu") t]
     ["destruct as           desa<C-BS>"  (holes-insert-and-expand "desa") t]
     ["discriminate           dis<C-BS>"  (holes-insert-and-expand "dis") t]
     ["eauto                   ea<C-BS>"  (holes-insert-and-expand "ea") t]
     ["eauto with             eaw<C-BS>"  (holes-insert-and-expand "dec") t]
     ["elim                     e<C-BS>"  (holes-insert-and-expand "e") t]
     ["elim using             elu<C-BS>"  (holes-insert-and-expand "elu") t]
     ["exists                  ex<C-BS>"  (holes-insert-and-expand "ex") t]
     ["field                  fld<C-BS>"  (holes-insert-and-expand "fld") t]
     ["firstorder            fsto<C-BS>"  (holes-insert-and-expand "fsto") t]
     ["fourier                fou<C-BS>"  (holes-insert-and-expand "fou") t]
     ["functional induction    fi<C-BS>"  (holes-insert-and-expand "fi") t]
     )

    ("INSERT TACTIC (g-z)" 
     "TACTIC           ABBREVIATION"
     ["generalize             g<C-BS>"  (holes-insert-and-expand "g") t]
     ["induction              ind<C-BS>"  (holes-insert-and-expand "ind") t]
     ["injection              inj<C-BS>"  (holes-insert-and-expand "inj") t]
     ["intro (smart)" coq-intros t]
     ["intro                  i<C-BS>"  (holes-insert-and-expand "i") t]
     ["intros                 is<C-BS>"  (holes-insert-and-expand "is") t]
     ["intuition              intu<C-BS>"  (holes-insert-and-expand "intu") t]
     ["inversion              inv<C-BS>"  (holes-insert-and-expand "inv") t]
     ["omega                  om<C-BS>"  (holes-insert-and-expand "om") t]
     ["pose                   po<C-BS>"  (holes-insert-and-expand "om") t]
     ["reflexivity            refl<C-BS>"  (holes-insert-and-expand "refl") t]
     ["replace                rep<C-BS>"  (holes-insert-and-expand "rep") t]
     ["rewrite                r<C-BS>"  (holes-insert-and-expand "r") t]
     ["rewrite in             ri<C-BS>"  (holes-insert-and-expand "ri") t]
     ["rewrite <-             r<<C-BS>"  (holes-insert-and-expand "rl") t]
     ["rewrite <- in          ri<<C-BS>"  (holes-insert-and-expand "ril") t]
     ["set                    set<C-BS>"  (holes-insert-and-expand "set") t]
     ["set in hyp             seth<C-BS>"  (holes-insert-and-expand "seth") t]
     ["set in goal            setg<C-BS>"  (holes-insert-and-expand "setg") t]
     ["set in                 seti<C-BS>"  (holes-insert-and-expand "seti") t]
     ["simpl                  s<C-BS>"  (holes-insert-and-expand "s") t]
     ["simpl                  si<C-BS>"  (holes-insert-and-expand "si") t]
     ["split                  sp<C-BS>"  (holes-insert-and-expand "sp") t]
     ["subst                  su<C-BS>"  (holes-insert-and-expand "su") t]
     ["symmetry               sym<C-BS>"  (holes-insert-and-expand "sym") t]
     ["transitivity           trans<C-BS>"  (holes-insert-and-expand "trans") t]
     ["trivial                t<C-BS>"  (holes-insert-and-expand "t") t]
     ["tauto                  ta<C-BS>"  (holes-insert-and-expand "ta") t]
     ["unfold                 u<C-BS>"  (holes-insert-and-expand "u") t]
     )
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
     "Replace hole with mouse: C-M-Shift select"  ;; da: does this one work??
     )

    ;; da: I also added abbrev submenu.  Surprising Emacs doesn't have one?
    ("Abbrevs"
     ["Expand at point" expand-abbrev t]
     ["Unexpand last" unexpand-abbrev t]
     ["List abbrevs" list-abbrevs t]
     ["Edit abbrevs" edit-abbrevs t]    ;; da: is it OK to add edit?
     ["Abbrev mode" abbrev-mode 
      :style toggle
      :selected (and (boundp 'abbrev-mode) abbrev-mode)])
    ;; With all these submenus you have to wonder if these things belong
    ;; on the main menu.  Are they the most often used?
    ["Compile" coq-Compile t]
    ["Set coq prog name for this file persistently" coq-ask-insert-coq-prog-name t]
    ))

;; da: Moved this from the main menu to the Help submenu.  
;; It also appears under Holes, anyway.
(defpgdefault help-menu-entries
  '(["Tell me about holes?" holes-show-doc t]))


(provide 'coq-abbrev)

