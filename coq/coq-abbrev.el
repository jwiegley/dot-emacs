;; default abbrev table
; This is for coq V8, Should test coq version
;(defvar coq-version-is-V74 nil)
;(defvar coq-version-is-V7 nil)
;(defvar coq-version-is-V6 nil)

(if (boundp 'holes-abbrev-complete)
	 (define-abbrev-table 'coq-mode-abbrev-table
		'(
		  ("u" "unfold" nil 0)
		  ("si" "simpl" nil 0)
		  ("t" "trivial" nil 0)
		  ("dec" "decompose []" nil 0)
		  ("ab" "absurd" nil 0)
		  ("ao" "abstract omega" nil 0)
		  ("s" "simpl" nil 0)
		  ("r<" "rewrite <-" nil 0)
		  ("r" "rewrite" nil 0)
		  ("di" "discriminate" nil 0)
		  ("p" "Print" nil 0)
		  ("indv" "Inductive" nil 0)
		  ("o" "abstract omega" nil 0)
		  ("l" "Lemma  :" nil 0)
		  ("awa" "auto with arith" nil 0)
		  ("i" "intro" nil 0)
		  ("h" "Hints  : ." nil 0)
		  ("g" "generalize" nil 0)
		  ("con" "constructor" nil 0)
		  ("e" "elim" nil 0)
		  ("ge" "generalize" nil 0)
		  ("sym" "symmetry" nil 0)
		  ("a" "auto" nil 0)
		  ("re" "rewrite" nil 0)
		  ("eawa" "eauto with arith" nil 0)
		  ("un" "unfold" nil 0)
		  ("eaw" "eauto with" nil 0)
		  ("f" "forall #:#,#" nil 0)
		  ("fi" "functional induction" nil 0)
		  ("fs" "Functional Scheme xxx := Induction for yyy (opt:with ...)." nil 0)
		  ("sc" "Scheme := Induction for Sort ." nil 0)
		  ("f" "fun (:) => " nil 0)
		  ("eap" "eapply" nil 0)
		  ("ex" "exists" nil 0)
		  ("inv" "inversion" nil 0)
		  ("is" "intros" nil 0)
		  ("abs" "absurd" nil 0)
		  ("tr" "trivial" nil 0)
		  ("in" "intro" nil 0)
		  ("dis" "discriminate" nil 0)
		  ("aw" "auto with" nil 0)
		  ("pr" "Print" nil 0)
		  ("au" "auto" nil 0)
		  ("as" "assumption" nil 0)
		  ("sy" "symmetry" nil 0)
		  ("el" "elim" nil 0)
		  ("ap" "apply" nil 0)
		  ("gen" "generalize" nil 0)
		  ("hr" "Hint Resolve :." nil 0)
		  ("ind" "induction" nil 0)
		  ("fix" "Fixpoint X (X : X) {struct X} : X := X." nil 0)
		  ("re<" "rewrite <-" nil 0)
		  ("ea" "eauto" nil 0)
		  ("def" "Definition : :=." nil 0)
		  ))
  (define-abbrev-table 'coq-mode-abbrev-table
	 '(
		("m" "match # with 
# => #" holes-abbrev-complete 1)
		("m|" "match # with 
 # => #
| # => #" holes-abbrev-complete 1)
		("m||" "match # with 
  # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("m|||" "match # with 
  # => #
| # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("m||||" "match # with 
  # => #
| # => #
| # => #
| # => #
| # => #" holes-abbrev-complete 1)
		("c" "cases #" holes-abbrev-complete 1)
		("u" "unfold #" holes-abbrev-complete 1)
		("si" "simpl" holes-abbrev-complete 0)
		("t" "trivial" holes-abbrev-complete 1)
		("dec" "decompose [#] #" holes-abbrev-complete 3)
		("ab" "absurd #" holes-abbrev-complete 0)
		("om" "abstract Omega" holes-abbrev-complete 0)
		("s" "simpl" holes-abbrev-complete 23)
		("r<" "rewrite <- #" holes-abbrev-complete 0)
		("r" "rewrite #" holes-abbrev-complete 19)
		("di" "discriminate" holes-abbrev-complete 0)
		("p" "Print #" holes-abbrev-complete 3)
		("indv" "Inductive # : # := #." holes-abbrev-complete 0)
		("indv|" "Inductive # : # :=
  # : #
| # : #." holes-abbrev-complete 0)
		("indv||" "Inductive # : # :=
  # : #
| # : #
| # : #." holes-abbrev-complete 0)
		("indv|||" "Inductive # : # :=
  # : #
| # : #
| # : #
| # : #." holes-abbrev-complete 0)
		("indv||||" "Inductive # : # :=
  # : #
| # : #
| # : #
| # : #
| # : #." holes-abbrev-complete 0)
		("o" "abstract omega" holes-abbrev-complete 0)
		("l" "Lemma # : #." holes-abbrev-complete 4)
		("awa" "auto with arith" holes-abbrev-complete 4)
		("i" "intro #" holes-abbrev-complete 10)
		("h" "Hints # : #." holes-abbrev-complete 0)
		("g" "generalize #" holes-abbrev-complete 0)
		("fo" "forall #,#" holes-abbrev-complete 0)
		("fo:" "forall #:#,#" holes-abbrev-complete 0)
		("fo::" "forall (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo:::" "forall (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("fo::::" "forall (#:#) (#:#) (#:#) (#:#), #" holes-abbrev-complete 0)
		("f" "fun # => #" holes-abbrev-complete 0)
		("f:" "fun #:# => #" holes-abbrev-complete 0)
		("f::" "fun (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f:::" "fun (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("f::::" "fun (#:#) (#:#) (#:#) (#:#) => #" holes-abbrev-complete 0)
		("e" "elim #" holes-abbrev-complete 1)
		("con" "constructor" holes-abbrev-complete 3)
		("ge" "generalize #" holes-abbrev-complete 0)
		("sym" "symmetry" holes-abbrev-complete 0)
		("a" "auto" holes-abbrev-complete 4)
		("re" "rewrite #" holes-abbrev-complete 0)
		("eawa" "eauto with arith" holes-abbrev-complete 0)
		("un" "unfold #" holes-abbrev-complete 7)
		("eaw" "eauto with #" holes-abbrev-complete 0)
		("fi" "functional induction #" holes-abbrev-complete 0)
		("fs" "Functional Scheme # := Induction for #." 
		 holes-abbrev-complete 0)
		("fsw" "Functional Scheme # := Induction for # with #." 
		 holes-abbrev-complete 0)
		("sc" "Scheme # := Induction for # Sort #." nil 0)
		("eap" "eapply #" holes-abbrev-complete 0)
		("ex" "exists #" holes-abbrev-complete 0)
		("inv" "inversion #" holes-abbrev-complete 9)
		("is" "intros #" holes-abbrev-complete 11)
		("abs" "absurd #" holes-abbrev-complete 0)
		("tr" "trivial" holes-abbrev-complete 7)
		("in" "intro" holes-abbrev-complete 1)
		("dis" "discriminate" holes-abbrev-complete 0)
		("aw" "auto with #" holes-abbrev-complete 1)
		("pr" "print #" holes-abbrev-complete 2)
		("au" "auto" holes-abbrev-complete 1)
		("as" "assumption" holes-abbrev-complete 4)
		("sy" "symmetry" holes-abbrev-complete 0)
		("el" "elim #" holes-abbrev-complete 0)
		("ap" "apply #" holes-abbrev-complete 16)
		("gen" "generalize #" holes-abbrev-complete 0)
		("hr" "Hint Resolve : #." holes-abbrev-complete 0)
		("ind" "induction #" holes-abbrev-complete 2)
		("fix" "Fixpoint # (#:#) {struct #} : # :=" holes-abbrev-complete 3)
		("re<" "rewrite <- #" holes-abbrev-complete 0)
		("ea" "eauto" holes-abbrev-complete 0)
		("def" "Definition #:# := #." holes-abbrev-complete 5)
		("def2" "Definition # (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def3" "Definition # (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		("def4" "Definition # (# : #) (# : #) (# : #) (# : #):# := #." holes-abbrev-complete 5)
		)
	 )
  )


