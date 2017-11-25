(*** company-coq—term-builder ***)

(*! This file demonstrates the evolution of a proof term,
    as one steps through a proof. !*)

(** Before stepping through this file, run the following (‘M-:’):
      (load-file "company-coq-term-builder.el") *)

Definition ExampleFunction : nat -> nat.
Proof.
  intros.
  refine (S _).
  refine (_ - 1).

  refine (3 * _).
  destruct H.
  + refine (1 + _).
    apply 0.
  + refine (2 + _).
    destruct H.
    * refine (3 + _).
      apply 0.
    * refine (4 + _).
      apply 1.
Defined.

Print ExampleFunction.
