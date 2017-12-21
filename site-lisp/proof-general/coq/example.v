(*
    Example proof script for Coq Proof General.

    $Id$
*)

Module Example.

  Lemma and_commutative : forall (A B:Prop),(A /\ B) -> (B /\ A).
  Proof.
    intros A B H.
    destruct H.
    split.
      trivial.
    trivial.
  Qed.

End Example.
