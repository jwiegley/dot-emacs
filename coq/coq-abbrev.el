;; default abbrev table
; This is for coq V8, Should test coq version
;(defvar coq-version-is-V74 nil)
;(defvar coq-version-is-V7 nil)
;(defvar coq-version-is-V6 nil)

(if (boundp 'holes-abbrev-complete)
	 (define-abbrev-table 'coq-mode-abbrev-table
		'(
		  ("a" "auto" nil 0)
		  ("ab" "absurd" nil 0)
		  ("abs" "absurd" nil 0)
		  ("ao" "abstract omega" nil 0)
		  ("ap" "apply" nil 0)
		  ("as" "assumption" nil 0)
		  ("au" "auto" nil 0)
		  ("aw" "auto with" nil 0)
		  ("awa" "auto with arith" nil 0)
		  ("con" "constructor" nil 0)
		  ("dec" "decompose []" nil 0)
		  ("def" "Definition : :=." nil 0)
		  ("di" "discriminate" nil 0)
		  ("dis" "discriminate" nil 0)
		  ("e" "elim" nil 0)
		  ("ea" "eauto" nil 0)
		  ("eap" "eapply" nil 0)
		  ("eaw" "eauto with" nil 0)
		  ("eawa" "eauto with arith" nil 0)
		  ("el" "elim" nil 0)
		  ("ex" "exists" nil 0)
		  ("f" "forall #:#,#" nil 0)
		  ("f" "fun (:) => " nil 0)
		  ("fi" "functional induction" nil 0)
		  ("fix" "Fixpoint X (X : X) {struct X} : X := X." nil 0)
		  ("fs" "Functional Scheme xxx := Induction for yyy (opt:with ...)." nil 0)
		  ("g" "generalize" nil 0)
		  ("ge" "generalize" nil 0)
		  ("gen" "generalize" nil 0)
		  ("h" "Hints  : ." nil 0)
		  ("hr" "Hint Resolve :." nil 0)
		  ("i" "intro" nil 0)
		  ("in" "intro" nil 0)
		  ("ind" "induction" nil 0)
		  ("indv" "Inductive" nil 0)
		  ("inv" "inversion" nil 0)
		  ("is" "intros" nil 0)
		  ("l" "Lemma  :" nil 0)
		  ("o" "abstract omega" nil 0)
		  ("p" "Print" nil 0)
		  ("pr" "Print" nil 0)
		  ("r" "rewrite" nil 0)
		  ("r<" "rewrite <-" nil 0)
		  ("re" "rewrite" nil 0)
		  ("re<" "rewrite <-" nil 0)
		  ("s" "simpl" nil 0)
		  ("sc" "Scheme := Induction for Sort ." nil 0)
		  ("si" "simpl" nil 0)
		  ("sy" "symmetry" nil 0)
		  ("sym" "symmetry" nil 0)
		  ("t" "trivial" nil 0)
		  ("tr" "trivial" nil 0)
		  ("u" "unfold" nil 0)
		  ("un" "unfold" nil 0)
		  ))
  (define-abbrev-table 'coq-mode-abbrev-table
	 '(
		("a" "auto" holes-abbrev-complete 4)
		("ab" "absurd #" holes-abbrev-complete 0)
		("abs" "absurd #" holes-abbrev-complete 0)
		("ap" "apply #" holes-abbrev-complete 16)
		("as" "assumption" holes-abbrev-complete 4)
		("au" "auto" holes-abbrev-complete 1)
		("aw" "auto with #" holes-abbrev-complete 1)
		("awa" "auto with arith" holes-abbrev-complete 4)
		("c" "cases #" holes-abbrev-complete 1)
		("con" "constructor" holes-abbrev-complete 3)
		("dec" "decompose [#] #" holes-abbrev-complete 3)
		("def" "Definition #:# := #." holes-abbrev-complete 5)
		("def2" "Definition # (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def3" "Definition # (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("di" "discriminate" holes-abbrev-complete 0)
		("dis" "discriminate" holes-abbrev-complete 0)
		("e" "elim #" holes-abbrev-complete 1)
		("ea" "eauto" holes-abbrev-complete 0)
		("eap" "eapply #" holes-abbrev-complete 0)
		("eaw" "eauto with #" holes-abbrev-complete 0)
		("eawa" "eauto with arith" holes-abbrev-complete 0)
		("el" "elim #" holes-abbrev-complete 0)
		("elu" "elim # using #" holes-abbrev-complete 0)
		("ex" "exists #" holes-abbrev-complete 0)
		("f" "fun # => #" holes-abbrev-complete 0)
		("f1" "fun #:# => #" holes-abbrev-complete 0)
		("f2" "fun (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f3" "fun (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f4" "fun (#:#) (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("fi" "functional induction #" holes-abbrev-complete 0)
		("fix" "Fixpoint # (#:#) {struct #} : # :=" holes-abbrev-complete 3)
		("fo" "forall #,#" holes-abbrev-complete 0)
		("fo1" "forall #:#,#" holes-abbrev-complete 0)
		("fo2" "forall (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo3" "forall (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo4" "forall (#:#) (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("fs" "Functional Scheme # := Induction for #." holes-abbrev-complete 0)
		("fsw" "Functional Scheme # := Induction for # with #." holes-abbrev-complete 0)
		("g" "generalize #" holes-abbrev-complete 0)
		("ge" "generalize #" holes-abbrev-complete 0)
		("gen" "generalize #" holes-abbrev-complete 0)
		("he" "Hint # : # := Extern # # #." holes-abbrev-complete 0)
		("hi" "Hint Immediate #: #." holes-abbrev-complete 0)
		("hr" "Hint Resolve #: #." holes-abbrev-complete 0)
		("hs" "Hints # : #." holes-abbrev-complete 0)
		("hu" "Hint Unfold #: #." holes-abbrev-complete 0)
		("i" "intro #" holes-abbrev-complete 10)
		("if" "if # then # else #" holes-abbrev-complete 1)
		("in" "intro" holes-abbrev-complete 1)
		("ind" "induction #" holes-abbrev-complete 2)
		("indv" "Inductive # : # := # : #." holes-abbrev-complete 0)
		("inv" "inversion #" holes-abbrev-complete 9)
		("is" "intros #" holes-abbrev-complete 11)
		("ite" "if # then # else #" holes-abbrev-complete 1)
		("l" "Lemma # : #." holes-abbrev-complete 4)
		("li" "let # := # in #" holes-abbrev-complete 1)
		("o" "omega" holes-abbrev-complete 0)
		("om" "Omega" holes-abbrev-complete 0)
		("p" "Print #" holes-abbrev-complete 3)
		("pr" "print #" holes-abbrev-complete 2)
		("r" "rewrite #" holes-abbrev-complete 19)
		("r<" "rewrite <- #" holes-abbrev-complete 0)
		("re" "rewrite #" holes-abbrev-complete 0)
		("re<" "rewrite <- #" holes-abbrev-complete 0)
		("s" "simpl" holes-abbrev-complete 23)
		("sc" "Scheme # := Induction for # Sort #." nil 0)
		("si" "simpl" holes-abbrev-complete 0)
		("sp" "Split" holes-abbrev-complete 1)
		("sy" "symmetry" holes-abbrev-complete 0)
		("sym" "symmetry" holes-abbrev-complete 0)
		("t" "trivial" holes-abbrev-complete 1)
		("tr" "trivial" holes-abbrev-complete 7)
		("u" "unfold #" holes-abbrev-complete 1)
		("un" "unfold #" holes-abbrev-complete 7)
		("m" "match # with 
# => #" holes-abbrev-complete 1)
		("m2" "match # with 
 # => #
| # => #" holes-abbrev-complete 1)
		("m3" "match # with 
  # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("m4" "match # with 
  # => #
| # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("m5" "match # with 
  # => #
| # => #
| # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("indv2" "Inductive # : # :=
  # : #
| # : #." holes-abbrev-complete 0)
		("indv3" "Inductive # : # :=
  # : #
| # : #
| # : #." holes-abbrev-complete 0)
		("indv4" "Inductive # : # :=
  # : #
| # : #
| # : #
| # : #." holes-abbrev-complete 0)
		("indv5" "Inductive # : # :=
  # : #
| # : #
| # : #
| # : #
| # : #." holes-abbrev-complete 0)
		)
	 )
  )


