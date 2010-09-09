Require Import Arith.


Function div2 (n : nat) {struct n}: nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
  end.


Module toto.
  Lemma l1: forall n:nat, n = n. 
    toto.
  Qed.
  Lemma l2: forall n:nat, n = n. 
  toto. Qed.
  Lemma l3: forall n:nat, n <= n. intro. Qed.
  Lemma l4: forall n:nat, n <= n. Proof. intro. Qed.
  Lemma l5 : forall n:nat, n <= n.
  Proof. intro.
  Qed.
  Lemma l6: forall n:nat, n = n. 
    toto.
    Lemma l7: forall n:nat, n = n. 
      toto.
    Qed.
  Qed.
End toto.

