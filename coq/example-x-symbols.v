(*
    Example uses of X-Symbol symbols in Coq.
    See README.

    Pierre Courtieu

    $Id$
*)

Fixpoint toto (x:nat) {struct x} : nat := (* nat should appear as |N *)
  match x with
    | O => O        (* double arrow here *)
    | S y => toto y (* double arrow here *)
  end.

Lemma titi : forall x:nat,x=x. (* symbolique for-all and nat *)
Admitted. 

(* this should appear like foo'a'1_B_3 where a and B are greek *)
Variable foo'alpha'1_beta_3 : Set.  

Fixpoint pow (n m:nat) {struct n} : nat :=
  match n with
	 | O => 0
	 | S p => m * pow p m
  end.

Notation " a ,{ b }  " := (a - b)
  (at level 1, no associativity).

Notation "a ^^ b" := (pow a b)
  (at level 1, no associativity).

Notation "a ^{ b }" := (pow a b)
  (at level 1, no associativity).


Variable delta:nat.

(* greek delta with a sub 1 and the same with super 1 *)
Definition delta__1 := 0. 
Definition delta__2 := delta^^1.
Definition delta__3 := delta__2^{delta}.

Parameter a b x:nat.
(* x with a+b subscripted and then superscripted *)
Definition x_a_b':= x^{a+b}. 
Definition x_a_b := x,{a+b}.
Definition x_a_b'' := x,{a+b}^{a*b}.

(* no greek letter should appear on this next line! *)
Variable philosophi   : Set.

(* same here *)
Variable aalpha alphaa : Set.


(* _a where a is greek *)
Variable _alpha : Set.

(* a_ where a is greek *)
Variable alpha_ : Set.

Lemma gamma__neqn : forall n__i:nat, n__i=n__i.


alpha lhd rhd lambda forall exists exists exist 
