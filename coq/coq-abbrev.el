;; default abbrev table
; This is for coq V8, you should test coq version before loading

;#s are replaced by holes by holes-abbrev-complete
(if (boundp 'holes-abbrev-complete)
	 ()
  (define-abbrev-table 'coq-mode-abbrev-table
	 '(
		("a" "auto" holes-abbrev-complete 4)
		("ar" "autorewrite with @{db,db...} using @{tac}" holes-abbrev-complete 1)
		("ab" "absurd " holes-abbrev-complete 0)
		("abs" "absurd " holes-abbrev-complete 0)
		("ap" "apply " holes-abbrev-complete 16)
		("as" "assumption" holes-abbrev-complete 4)
		("ass" "assert ( # : # )" holes-abbrev-complete 4)
		("au" "auto" holes-abbrev-complete 1)
		("aw" "auto with " holes-abbrev-complete 1)
		("awa" "auto with arith" holes-abbrev-complete 4)
		("c" "cases " holes-abbrev-complete 1)
		("ch" "change " holes-abbrev-complete 1)
		("chi" "change # in #" holes-abbrev-complete 1)
		("chwi" "change # with # in #" holes-abbrev-complete 1)
		("con" "constructor" holes-abbrev-complete 3)
		("cong" "congruence" holes-abbrev-complete 3)
		("dec" "decompose [#] @{hyp}" holes-abbrev-complete 3)
		("def" "Definition #:# := #." holes-abbrev-complete 5)
		("def2" "Definition # (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def3" "Definition # (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("deg" "decide equality" holes-abbrev-complete 3)
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
		("inf" "infix \"#\" := # (at level #) : @{scope}." holes-abbrev-complete 1)
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
		("notsl" "Notation Local # := #." holes-abbrev-complete 0)
		("not" "Notation \"#\" := # (at level #, # at level #)." holes-abbrev-complete 0)
		("nota" "Notation \"#\" := # (at level #, # at level #)." holes-abbrev-complete 0)
		("notas" "Notation \"#\" := # (at level #, # associativity)." holes-abbrev-complete 0)
		("notasc" "Notation \"#\" := # (at level #, # at level #) : @{scope}." holes-abbrev-complete 0)
		("notassc" "Notation \"#\" := # (at level #, # associativity) : @{scope}." holes-abbrev-complete 0)
		("o" "omega" holes-abbrev-complete 0)
		("om" "omega" holes-abbrev-complete 0)
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
    ("Insert Command" 
      "COMMAND               ABBREVIATION"
     ["Definition            def<C-BS>" (insert-and-expand "def") t]
     ["Fixpoint              fix<C-BS>" (insert-and-expand "fix") t]
     ["Lemma                 l<C-BS>" (insert-and-expand "l") t]
     ""
     ["Inductive             indv<C-BS>" (insert-and-expand "indv") t]
     ["Inductive1            indv1<C-BS>" (insert-and-expand "indv1") t]
     ["Inductive2             indv2<C-BS>" (insert-and-expand "indv2") t]
     ["Inductive3            indv3<C-BS>" (insert-and-expand "indv3") t]
     ["Inductive4            indv4<C-BS>" (insert-and-expand "indv4") t]
     ""
     ["Section..." coq-insert-section t]
     ""
     ("Modules"
      "COMMAND               ABBREVIATION"
      ["Module (interactive)... " coq-insert-module t]
      ["Module                mo<C-BS>" (insert-and-expand "mo") t]
      ["Module (<:)           mo2<C-BS>" (insert-and-expand "mo") t]
;      ["Module (interactive)  moi<C-BS>" (insert-and-expand "moi") t]
;      ["Module (interactive <:) moi2<C-BS>" (insert-and-expand "moi2") t]
      ["Module Type           mt<C-BS>" (insert-and-expand "mt") t]
;      ["Module Type (interactive) mti<C-BS>" (insert-and-expand "mti") t]
;      ""
      ["Declare Module        dm<C-BS>" (insert-and-expand "dm") t]
      ["Declare Module (<:)   dm2<C-BS>" (insert-and-expand "dm") t]
;      ["Declare Module (inter.) dmi<C-BS>" (insert-and-expand "dmi") t]
;      ["Declare Module (inter. <:) dmi2<C-BS>" (insert-and-expand "dmi2") t]
      )
     ("Hints"
      "COMMAND               ABBREVIATION"
      ["Hint Constructors     hc<C-BS>" (insert-and-expand "hc") t]
      ["Hint Immediate        hi<C-BS>" (insert-and-expand "hi") t]
      ["Hint Resolve          hr<C-BS>" (insert-and-expand "hr") t]
      ["Hint Rewrite          hrw<C-BS>" (insert-and-expand "hrw") t]
      ["Hint Extern           he<C-BS>" (insert-and-expand "he") t]
     )
     ("Schemes"
      "COMMAND               ABBREVIATION"
      ["Scheme                sc<C-BS>" (insert-and-expand "sc") t]
      ["Functional Scheme     fs<C-BS>" (insert-and-expand "fs") t]
      ["Functional Scheme with    fsw<C-BS>" (insert-and-expand "fsw") t]
      )
     ("Notations"
      "COMMAND               ABBREVIATION"
      ["infix                           inf<C-BS>" (insert-and-expand "inf") t]     
      ["Notation (no assoc)             nota<C-BS>" (insert-and-expand "nota") t]     
      ["Notation (assoc)                notas<C-BS>" (insert-and-expand "notas") t]     
      ["Notation (no assoc, scope)      notasc<C-BS>" (insert-and-expand "notasc") t]     
      ["Notation (assoc, scope)         notassc<C-BS>" (insert-and-expand "notassc") t]
		""
      ["Notation (simple)               nots<C-BS>" (insert-and-expand "nots") t]     
      ["Notation (simple,local)         notsl<C-BS>" (insert-and-expand "nots") t]     

      )
     )

    ("Insert term" 
     "FORM           ABBREVIATION"
     ["forall        fo<C-BS>"  (insert-and-expand "fo") t]
     ["forall1       fo1<C-BS>"  (insert-and-expand "fo1") t]
     ["forall2       fo2<C-BS>" (insert-and-expand "fo2") t]
     ["forall3       fo3<C-BS>" (insert-and-expand "fo3") t]
     ["forall4       fo4<C-BS>" (insert-and-expand "fo4") t]
     ""
     ["fun           f<ctrl-bacspace>"  (insert-and-expand "f") t]
     ["fun1          f1<ctrl-bacspace>"  (insert-and-expand "f1") t]
     ["fun2          f2<C-BS>" (insert-and-expand "f2") t]
     ["fun3          f3<C-BS>" (insert-and-expand "f3") t]
     ["fun4          f4<C-BS>" (insert-and-expand "f4") t]
     ""
     ["if then else  if<C-BS>"  (insert-and-expand "li") t]
     ["let in        li<C-BS>"  (insert-and-expand "li") t]
     ""
     ["match         m<C-BS>"  (insert-and-expand "m") t]
     ["match2        m2<C-BS>"  (insert-and-expand "m2") t]
     ["match3        m3<C-BS>"  (insert-and-expand "m3") t]
     ["match4        m4<C-BS>"  (insert-and-expand "m4") t]
     )

    ("Insert tactic (a-f)" 
     "TACTIC           ABBREVIATION"
     ["absurd                 abs<C-BS>"  (insert-and-expand "abs") t]
     ["assumption              as<C-BS>"  (insert-and-expand "as") t]
     ["assert                 ass<C-BS>"  (insert-and-expand "ass") t]
     ["auto                     a<C-BS>"  (insert-and-expand "a") t]
     ["auto with               aw<C-BS>"  (insert-and-expand "aw") t]
     ["auto with arith        awa<C-BS>"  (insert-and-expand "awa") t]
     ["autorewrite             ar<C-BS>"  (insert-and-expand "ar") t]
     ["cases                    c<C-BS>"  (insert-and-expand "c") t]
     ["change                  ch<C-BS>"  (insert-and-expand "ch") t]
     ["change in              chi<C-BS>"  (insert-and-expand "chi") t]
     ["change with in        chwi<C-BS>"  (insert-and-expand "chwi") t]
     ["constructor            con<C-BS>"  (insert-and-expand "con") t]
     ["congruence            cong<C-BS>"  (insert-and-expand "cong") t]
     ["decompose              dec<C-BS>"  (insert-and-expand "dec") t]
     ["decide equality        deg<C-BS>"  (insert-and-expand "deg") t]
     ["destruct               des<C-BS>"  (insert-and-expand "des") t]
     ["destruct using        desu<C-BS>"  (insert-and-expand "desu") t]
     ["destruct as           desa<C-BS>"  (insert-and-expand "desa") t]
     ["discriminate           dis<C-BS>"  (insert-and-expand "dis") t]
     ["eauto                   ea<C-BS>"  (insert-and-expand "ea") t]
     ["eauto with             eaw<C-BS>"  (insert-and-expand "dec") t]
     ["elim                     e<C-BS>"  (insert-and-expand "e") t]
     ["elim using             elu<C-BS>"  (insert-and-expand "elu") t]
     ["exists                  ex<C-BS>"  (insert-and-expand "ex") t]
     ["field                  fld<C-BS>"  (insert-and-expand "fld") t]
     ["firstorder            fsto<C-BS>"  (insert-and-expand "fsto") t]
     ["fourier                fou<C-BS>"  (insert-and-expand "fou") t]
     ["functional induction    fi<C-BS>"  (insert-and-expand "fi") t]
     )

    ("Insert tactic (g-z)" 
     "TACTIC           ABBREVIATION"
     ["generalize             g<C-BS>"  (insert-and-expand "g") t]
     ["induction              ind<C-BS>"  (insert-and-expand "ind") t]
     ["injection              inj<C-BS>"  (insert-and-expand "inj") t]
     ["intro                  i<C-BS>"  (insert-and-expand "i") t]
     ["intros                 is<C-BS>"  (insert-and-expand "is") t]
     ["intuition              intu<C-BS>"  (insert-and-expand "intu") t]
     ["inversion              inv<C-BS>"  (insert-and-expand "inv") t]
     ["omega                  om<C-BS>"  (insert-and-expand "om") t]
     ["pose                   po<C-BS>"  (insert-and-expand "om") t]
     ["reflexivity            refl<C-BS>"  (insert-and-expand "refl") t]
     ["replace                rep<C-BS>"  (insert-and-expand "rep") t]
     ["rewrite                r<C-BS>"  (insert-and-expand "r") t]
     ["rewrite in             ri<C-BS>"  (insert-and-expand "ri") t]
     ["rewrite <-             r<<C-BS>"  (insert-and-expand "rl") t]
     ["rewrite <- in          ri<<C-BS>"  (insert-and-expand "ril") t]
     ["set                    set<C-BS>"  (insert-and-expand "set") t]
     ["set in hyp             seth<C-BS>"  (insert-and-expand "seth") t]
     ["set in goal            setg<C-BS>"  (insert-and-expand "setg") t]
     ["set in                 seti<C-BS>"  (insert-and-expand "seti") t]
     ["simpl                  s<C-BS>"  (insert-and-expand "s") t]
     ["simpl                  si<C-BS>"  (insert-and-expand "si") t]
     ["split                  sp<C-BS>"  (insert-and-expand "sp") t]
     ["subst                  su<C-BS>"  (insert-and-expand "su") t]
     ["symmetry               sym<C-BS>"  (insert-and-expand "sym") t]
     ["transitivity           trans<C-BS>"  (insert-and-expand "trans") t]
     ["trivial                t<C-BS>"  (insert-and-expand "t") t]
     ["tauto                  ta<C-BS>"  (insert-and-expand "ta") t]
     ["unfold                 u<C-BS>"  (insert-and-expand "u") t]
     )

    ["What are those highlighted chars??" (holes-short-doc) t]
    ("holes" 
     "make a hole active   click on it"
     "disable a hole   click on it (button 2)"
     "destroy a hole   click on it (button 3)"
     "make a hole with mouse  C-M-select"
     ["make a hole at point   C-M-h"  (set-make-active-hole) t]
     ["make selection a hole  C-M-h"  (set-make-active-hole) t]
     ["replace active hole by selection C-M-y"  (replace-update-active-hole) t]
     "replace active hole with mouse  C-M-Shift select"
     ["jump to active hole M-return"  (set-point-next-hole-destroy) t]
     ["forget all holes in this buffer"  (clear-all-buffer-holes) t]
     ["What are those holes?" (holes-short-doc) t]
     )
    ["expand abbrev at point" expand-abbrev t]
    ["list abbrevs" list-abbrevs t]
    ["Print..." coq-Print t]
    ["Check..." coq-Check t]
    ["Hints" coq-PrintHint t]
    ["Show ith goal..." coq-Show t]
    ["Search isos/pattern..." coq-SearchIsos t]
    ["3 buffers view" coq-three-b t]
    ["Compile" coq-Compile t] ))

(provide 'coq-abbrev)

