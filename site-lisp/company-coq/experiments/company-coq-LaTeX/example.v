(***    company-coq—LaTeX    ***)


(*+ What happens if we use Coq notations +*)
(*+        to produce LaTeX code?        +*)


(*!   [nsum 0 n (fun x => f x)]  ↦  [\sum_{x = 0}^n f(x)] ?   !*)


(* Before stepping through this file, run the following (‘M-:’):
     (load-file "company-coq-latex.el") *)

(******************************************************************************)
(*! Preliminary setup: define a function and a notation !*)

(** We start by defining a function: *)

Require Import NArith ArithRing.

Fixpoint nsum max f :=
  match max with
  | O => f 0
  | S max' => f max + nsum max' f
  end.

(** And we add a notation for it: *)

Notation "'\ccNsum{' x '}{' max '}{' f '}'" := (nsum max (fun x => f)).

(* begin hide *)
Infix "\wedge" := and (at level 190, right associativity).
Notation "A \Rightarrow{} B" := (forall (_ : A), B) (at level 200, right associativity).
Notation "'\ccForall{' x .. y '}{' P '}'" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity, format "'\ccForall{' x .. y '}{' P '}'").
Notation "'\ccNat{}'" := nat.
Notation "'\ccSucc{' n '}'" := (S n).
Infix "\times" := mult (at level 30).
(* end hide *)

(******************************************************************************)
(*! Then the magic happens! !*)

Lemma Gauss: forall n, 2 * (nsum n (fun x => x)) = n * (n + 1).
  intros.
  induction n.
  - cbv [nsum].
    reflexivity.
  - unfold nsum; fold nsum.
    rewrite Mult.mult_plus_distr_l.
    rewrite IHn.
    ring.
Qed.

(******************************************************************************)
(*! Fractions work nicely as well: !*)

Require Import Coq.QArith.QArith Coq.QArith.Qring Coq.QArith.Qfield.

(* begin hide *)
Notation "'\ccQ{}'" := Q.
Notation "\ccPow{ x }{ y }" := (Qpower x y).
Notation "'\ccFrac{' x '}{' y '}'" := (Qdiv x y)  : Q_scope.
Infix "\le" := Qle (at level 100).
Infix "\equiv" := Qeq (at level 100).
Infix "\times" := Qmult (at level 30).
Notation "\ccNot{ x }" := (not x) (at level 100).
(* Notation "x '\not\equiv' y" := (not (Qeq x y)) (at level 100). *)

Lemma Qmult_Qdiv_fact :
  forall a b c, not (c == 0) -> a * (b / c) == (a * b) / c.
Proof. intros; field; assumption. Qed.

Lemma Qdiv_1 :
  forall a, a / 1 == a.
Proof. intros; field. Qed.

Lemma Qplus_le_0 :
  forall a b, 0 <= a -> 0 <= b -> 0 <= a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qplus_lt_0 :
  forall a b, 0 < a -> 0 <= b -> 0 < a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_lt_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qmult_0 :
  forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  rewrite <- (Qmult_lt_l _ _ _ Ha), Qmult_0_r in Hb; assumption.
Qed.

Lemma Qsqr_0 :
  forall a, 0 <= a ^ 2.
Proof.
  intros [n d].
  simpl; unfold Qmult, Qle; simpl.
  rewrite Z.mul_1_r; apply Z.ge_le, sqr_pos.
Qed.

Lemma Qgt_0_Qneq_0 :
  forall a, 0 < a -> not (a == 0).
Proof.
  intros [n d].
  unfold Qeq, Qlt; simpl.
  rewrite !Z.mul_1_r, Z.neg_pos_cases; intuition.
Qed.

Tactic Notation "Qside" "using" constr(lemma) :=
  try solve [repeat match goal with
                    | [ H: _ /\ _ |- _ ] => destruct H
                    end;
             auto using Qplus_le_0, Qmult_le_0_compat, Qmult_0,
             Qgt_0_Qneq_0, Qlt_le_weak, Qplus_lt_0, lemma].

Ltac Qside :=
  Qside using I.
(* end hide *)

Lemma Qfracs :
  forall a b c d,
    a > 0 /\ b > 0 /\ c > 0 /\ d > 0 ->
    (a + c)/(b + d) <= a/b + c/d.
Proof with Qside.
  intros a b c d H.
  field_simplify...
  rewrite <- Qmult_le_l with (z := b + d)...
  rewrite Qmult_div_r...
  rewrite Qmult_Qdiv_fact...
  rewrite <- Qmult_le_l with (z := b * d)...
  rewrite Qmult_div_r...
  field_simplify; rewrite !Qdiv_1...
  rewrite <- Qplus_le_l with (z := - b * d * a); ring_simplify.
  rewrite <- Qplus_le_l with (z := - b * d * c); ring_simplify.
  Qside using Qsqr_0.
Qed.

(******************************************************************************)
(*! And you can add tactic notations to the mix! !*)

Tactic Notation "reduce" "addition" :=
  field_simplify.
Tactic Notation "multiply" "each" "side" "by" constr(term) :=
  rewrite <- Qmult_le_l with (z := term).
Tactic Notation "cancel" "numerator" "and" "denominator" :=
  rewrite !Qmult_div_r.
Tactic Notation "harmonize" "fractions" :=
  rewrite !Qmult_Qdiv_fact.
Tactic Notation "expand" "and" "collect" :=
  field_simplify; rewrite !Qdiv_1.
Tactic Notation "subtract" constr(term) "on" "each" "side" :=
  rewrite <- Qplus_le_l with (z := - term); ring_simplify.
Tactic Notation "consequence" "of" constr(lemma) := Qside using lemma.

Lemma Qfracs_take_two :
  forall a b c d,
    a > 0 /\ b > 0 /\ c > 0 /\ d > 0 ->
    (a + c)/(b + d) <= a/b + c/d.
Proof with Qside.
  intros a b c d H.
  reduce addition...
  multiply each side by (b + d)...
  cancel numerator and denominator...
  harmonize fractions...
  multiply each side by (b * d)...
  cancel numerator and denominator...
  expand and collect...
  subtract (b * d * a) on each side...
  subtract (b * d * c) on each side...
  consequence of Qsqr_0...
Qed.