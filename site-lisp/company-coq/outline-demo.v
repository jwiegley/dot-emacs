Require Import Utf8 Omega NArith.

Lemma Lemma1 : ∀ x, x + 1 > x.
Proof.
  intros; intuition.
Qed.

Theorem Theorem1 : ∀ A, False -> A.
Proof.
  intros A H. destruct H.
Qed.

Goal ∃ x, x > 100.

Definition Definition1 x := S (S x).

Lemma a : True.
Proof with easy.
  idtac...
Qed.

Goal ∃ x, x > 100.
Abort.

  