;; default abbrev table
; This is for coq V7, you should test coq version before loading

;#s are replaced by holes by holes-abbrev-complete
(if (boundp 'holes-abbrev-complete)
	 ()
  (define-abbrev-table 'coq-mode-abbrev-table
	 '(
		("a" "Auto" holes-abbrev-complete 4)
		("ar" "Autorewrite [@{db,db...}] using @{tac}" holes-abbrev-complete 1)
		("ab" "Absurd " holes-abbrev-complete 0)
		("abs" "Absurd " holes-abbrev-complete 0)
		("ap" "Apply " holes-abbrev-complete 16)
		("as" "Assumption" holes-abbrev-complete 4)
		("au" "Auto" holes-abbrev-complete 1)
		("aw" "Auto with " holes-abbrev-complete 1)
		("awa" "Auto with arith" holes-abbrev-complete 4)
		("ch" "Change " holes-abbrev-complete 1)
		("chi" "Change # in #" holes-abbrev-complete 1)
		("chwi" "Change # with # in #" holes-abbrev-complete 1)
		("con" "Constructor" holes-abbrev-complete 3)
		("dec" "Decompose [#] @{hyp}" holes-abbrev-complete 3)
		("def" "Definition #:# := #." holes-abbrev-complete 5)
		("def1" "Definition # [# : #] :# := #." holes-abbrev-complete 5)
		("deg" "Decide Equality" holes-abbrev-complete 3)
		("des" "Destruct " holes-abbrev-complete 0)
		("desu" "Destruct # using #" holes-abbrev-complete 0)
		("desa" "Destruct # as #" holes-abbrev-complete 0)
		("dis" "Discriminate" holes-abbrev-complete 0)
		("dm" "Declare Module # : # := #." holes-abbrev-complete 0)
		("dm2" "Declare Module # <: # := #." holes-abbrev-complete 0)
		("dmi" "Declare Module # : #.\n#\nEnd #." holes-abbrev-complete 0)
		("dmi2" "Declare Module # <: #.\n#\nEnd #." holes-abbrev-complete 0)
		("e" "Elim #" holes-abbrev-complete 1)
		("ea" "Eauto" holes-abbrev-complete 0)
		("eap" "Eapply #" holes-abbrev-complete 0)
		("eaw" "Eauto with @{db}" holes-abbrev-complete 0)
		("eawa" "Eauto with arith" holes-abbrev-complete 0)
		("el" "Elim #" holes-abbrev-complete 0)
		("elu" "Elim # using #" holes-abbrev-complete 0)
		("ex" "Exists #" holes-abbrev-complete 0)
		("f" "[#:#]#" holes-abbrev-complete 0)
		("fix" "Fixpoint # [#:#] : # :=\n#." holes-abbrev-complete 3)
		("fo" "(#:#)#" holes-abbrev-complete 0)
		("fsto" "Firstorder" holes-abbrev-complete 0)
		("g" "Generalize #" holes-abbrev-complete 0)
		("ge" "Generalize #" holes-abbrev-complete 0)
		("gen" "Generalize #" holes-abbrev-complete 0)
		("hc" "Hints Constructors # : #." holes-abbrev-complete 0)
		("he" "Hint # : @{db} := Extern @{cost} (@{pat}) (@{tac})." holes-abbrev-complete 0)
		("hi" "Hints Immediate # : @{db}." holes-abbrev-complete 0)
		("hr" "Hints Resolve # : @{db}." holes-abbrev-complete 0)
		("hrw" "Hint Rewrite -> [@{t1 t2...}] in @{db} using @{tac}." holes-abbrev-complete 0)
		("hs" "Hints # : #." holes-abbrev-complete 0)
		("hu" "Hints Unfold # : #." holes-abbrev-complete 0)
		("i" "Intro " holes-abbrev-complete 10)
		("if" "if # then # else #" holes-abbrev-complete 1)
		("in" "Intro" holes-abbrev-complete 1)
		("ind" "Induction #" holes-abbrev-complete 2)
		("indv" "Inductive # : # := # : #." holes-abbrev-complete 0)
		("indv2" "Inductive # : # :=\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv3" "Inductive # : # :=\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv4" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("indv5" "Inductive # : # :=\n| # : #\n| # : #\n| # : #\n| # : #\n| # : #." holes-abbrev-complete 0)
		("inj" "Injection #" holes-abbrev-complete 2)
		("inv" "Inversion #" holes-abbrev-complete 9)
		("intu" "Intuition #" holes-abbrev-complete 9)
		("is" "Intros #" holes-abbrev-complete 11)
		("ite" "if # then # else #" holes-abbrev-complete 1)
		("l" "Lemma # : #." holes-abbrev-complete 4)
		("li" "Let # := # in #" holes-abbrev-complete 1)
		("c" "Cases # of\n| # => #\nend" holes-abbrev-complete 1)
		("c2" "Cases # of\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("c3" "Cases # of\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("c4" "Cases # of\n| # => #\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("c5" "Cases # of\n| # => #\n| # => #\n| # => #\n| # => #\n| # => #\nend" holes-abbrev-complete 1)
		("mt" "Module Type # := #." holes-abbrev-complete 0)
		("mti" "Module Type #.\n#\nEnd #." holes-abbrev-complete 0)
		("mo" "Module # : # := #." holes-abbrev-complete 0)
		("mo2" "Module # <: # := #." holes-abbrev-complete 0)
		("moi" "Module # : #.\n#\nEnd #." holes-abbrev-complete 0)
		("moi2" "Module # <: #.\n#\nEnd #." holes-abbrev-complete 0)
		("o" "Omega" holes-abbrev-complete 0)
		("om" "Omega" holes-abbrev-complete 0)
		("p" "Print #" holes-abbrev-complete 3)
		("po" "Pose ( # := # )" nil 0)
		("pr" "Print #" holes-abbrev-complete 2)
		("rep" "Replace # with #" holes-abbrev-complete 19)
		("r" "Rewrite #" holes-abbrev-complete 19)
		("r<" "Rewrite <- #" holes-abbrev-complete 0)
		("rl" "Rewrite <- #" holes-abbrev-complete 0)
		("refl" "Reflexivity #" holes-abbrev-complete 0)
		("ri" "Rewrite # in #" holes-abbrev-complete 19)
		("ril" "Rewrite <- # in #" holes-abbrev-complete 0)
		("ri<" "Rewrite <- # in #" holes-abbrev-complete 0)
		("re" "Rewrite #" holes-abbrev-complete 0)
		("re<" "Rewrite <- #" holes-abbrev-complete 0)
		("ring" "Ring #" holes-abbrev-complete 19)
		("s" "Simpl" holes-abbrev-complete 23)
		("su" "Subst #" holes-abbrev-complete 23)
		("sc" "Scheme @{name} := Induction for # Sort #." nil 0)
		("si" "Simpl" holes-abbrev-complete 0)
		("sp" "Split" holes-abbrev-complete 1)
		("sy" "Symmetry" holes-abbrev-complete 0)
		("sym" "Symmetry" holes-abbrev-complete 0)
		("t" "Trivial" holes-abbrev-complete 1)
		("tr" "Trivial" holes-abbrev-complete 1)
		("trans" "Transitivity #" holes-abbrev-complete 1)
		("ta" "Tauto" holes-abbrev-complete 1)
		("u" "Unfold #" holes-abbrev-complete 1)
		("un" "Unfold #" holes-abbrev-complete 7)
		("v" "Variable # : #." holes-abbrev-complete 7)
		("vs" "Variables # : #." holes-abbrev-complete 7)
		)
	 )
  )


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
      )
     )

    ("Insert term" 
     "FORM           ABBREVIATION"
     ["forall        fo<C-BS>"  (insert-and-expand "fo") t]
     ""
     ["fun           f<ctrl-bacspace>"  (insert-and-expand "f") t]
     ""
     ["let in        li<C-BS>"  (insert-and-expand "li") t]
     ""
     ["Cases         c<C-BS>"  (insert-and-expand "c") t]
     ["Cases2        c2<C-BS>"  (insert-and-expand "c2") t]
     ["Cases3        c3<C-BS>"  (insert-and-expand "c3") t]
     ["Cases4        c4<C-BS>"  (insert-and-expand "c4") t]
     )

    ("Insert tactic (a-f)" 
     "TACTIC           ABBREVIATION"
     ["Absurd                 abs<C-BS>"  (insert-and-expand "abs") t]
     ["Assumption              as<C-BS>"  (insert-and-expand "as") t]
     ["Assert                 ass<C-BS>"  (insert-and-expand "ass") t]
     ["Auto                     a<C-BS>"  (insert-and-expand "a") t]
     ["Auto with               aw<C-BS>"  (insert-and-expand "aw") t]
     ["Auto with arith        awa<C-BS>"  (insert-and-expand "awa") t]
     ["Autorewrite             ar<C-BS>"  (insert-and-expand "ar") t]
     ["Cases                    c<C-BS>"  (insert-and-expand "c") t]
     ["Change                  ch<C-BS>"  (insert-and-expand "ch") t]
     ["Change in              chi<C-BS>"  (insert-and-expand "chi") t]
     ["Change with in        chwi<C-BS>"  (insert-and-expand "chwi") t]
     ["Constructor            con<C-BS>"  (insert-and-expand "con") t]
     ["Congruence            cong<C-BS>"  (insert-and-expand "cong") t]
     ["Decompose              dec<C-BS>"  (insert-and-expand "dec") t]
     ["Decide Equality        deg<C-BS>"  (insert-and-expand "deg") t]
     ["Destruct               des<C-BS>"  (insert-and-expand "des") t]
     ["Destruct using        desu<C-BS>"  (insert-and-expand "desu") t]
     ["Destruct as           desa<C-BS>"  (insert-and-expand "desa") t]
     ["Discriminate           dis<C-BS>"  (insert-and-expand "dis") t]
     ["Eauto                   ea<C-BS>"  (insert-and-expand "ea") t]
     ["Eauto with             eaw<C-BS>"  (insert-and-expand "dec") t]
     ["Elim                     e<C-BS>"  (insert-and-expand "e") t]
     ["Elim using             elu<C-BS>"  (insert-and-expand "elu") t]
     ["Exists                  ex<C-BS>"  (insert-and-expand "ex") t]
     ["Field                  fld<C-BS>"  (insert-and-expand "fld") t]
     ["Firstorder            fsto<C-BS>"  (insert-and-expand "fsto") t]
     ["Fourier                fou<C-BS>"  (insert-and-expand "fou") t]
     )

    ("Insert tactic (g-z)" 
     "TACTIC           ABBREVIATION"
     ["Generalize             g<C-BS>"  (insert-and-expand "g") t]
     ["Induction              ind<C-BS>"  (insert-and-expand "ind") t]
     ["Injection              inj<C-BS>"  (insert-and-expand "inj") t]
     ["Intro                  i<C-BS>"  (insert-and-expand "i") t]
     ["Intros                 is<C-BS>"  (insert-and-expand "is") t]
     ["Intuition              intu<C-BS>"  (insert-and-expand "intu") t]
     ["Inversion              inv<C-BS>"  (insert-and-expand "inv") t]
     ["Omega                  om<C-BS>"  (insert-and-expand "om") t]
     ["Pose                   po<C-BS>"  (insert-and-expand "om") t]
     ["Reflexivity            refl<C-BS>"  (insert-and-expand "refl") t]
     ["Replace                rep<C-BS>"  (insert-and-expand "rep") t]
     ["Rewrite                r<C-BS>"  (insert-and-expand "r") t]
     ["Rewrite in             ri<C-BS>"  (insert-and-expand "ri") t]
     ["Rewrite <-             r<<C-BS>"  (insert-and-expand "rl") t]
     ["Rewrite <- in          ri<<C-BS>"  (insert-and-expand "ril") t]
     ["Simpl                  s<C-BS>"  (insert-and-expand "s") t]
     ["Simpl                  si<C-BS>"  (insert-and-expand "si") t]
     ["Split                  sp<C-BS>"  (insert-and-expand "sp") t]
     ["Subst                  su<C-BS>"  (insert-and-expand "su") t]
     ["Symmetry               sym<C-BS>"  (insert-and-expand "sym") t]
     ["Transitivity           trans<C-BS>"  (insert-and-expand "trans") t]
     ["Trivial                t<C-BS>"  (insert-and-expand "t") t]
     ["Tauto                  ta<C-BS>"  (insert-and-expand "ta") t]
     ["Unfold                 u<C-BS>"  (insert-and-expand "u") t]
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

(provide 'coq-abbrev-V7)

