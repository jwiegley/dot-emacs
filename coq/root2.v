(******************************************************************************
 *                                                                            *
 *    Proof that sqrt 2 is irrational                                         *
 *                                                                            *
 *                                              Laurent.Thery@sophia.inria.fr *
 *    February  2002                                                          *
 *   (Revised April 2004 for coq 8.0)                                         *
 ******************************************************************************)

Require Import ArithRing.
Require Import Wf_nat.
Require Import Peano_dec.
Require Import Div2.
Require Import Even.

(******************************************************************************
 *                                                                            *
 *    Properties of div2 and double (these theorems should be in Div2.v)      *
 *                                                                            *
 ******************************************************************************)
 
Theorem double_div2: forall (n : nat),  div2 (double n) = n.
simple induction n; auto with arith.
intros n0 H.
rewrite double_S; pattern n0 at 2; rewrite <- H; simpl; auto.
Qed.
 
Theorem double_inv: forall (n m : nat), double n = double m ->  n = m.
intros n m H; rewrite <- (double_div2 n); rewrite <- (double_div2 m); rewrite H;
 auto.
Qed.
 
Theorem double_mult_l: forall (n m : nat),  double (n * m) = double n * m.
unfold double; auto with arith.
Qed.
 
Theorem double_mult_r: forall (n m : nat),  double (n * m) = n * double m.
unfold double; intros; ring.
Qed.

(****************************************************************************** 
 *                                                                            *
 *    If the power to the 2 of a number is even, then this number is even     *
 *                                                                            *
 ******************************************************************************)
 
Theorem even_is_even_times_even: forall (n : nat), even (n * n) ->  even n.
intros n H; (try case (even_or_odd n)); auto.
intros; apply even_mult_inv_r with (1 := H); auto.
Qed.

(****************************************************************************** 
 *                                                                            *
 *       Useful fact 4*(n/2)*(n/2) = n*n if n is even                         *
 *                                                                            *
 ******************************************************************************)
 
Theorem main_thm_aux:
 forall (n : nat), even n ->  double (double (div2 n * div2 n)) = n * n.
intros; rewrite double_mult_l; rewrite double_mult_r;
 (repeat rewrite <- even_double); auto.
Qed.

(****************************************************************************** 
 * Main theorem                                                               *
 * We do the proof of the theorem by well founded induction:                  *
 *   Suppose that we have n*n = 2*p*p                                         *
 *    if n=0 then p = O                                                       *
 *    if n<>0 then                                                            *
 *       - n is even (n=2n') and p is even (p=2p')                            *
 *       - we have n'*n'=2*p'*p' and n' < n                                   *
 *       - by the induction hypothesis we have p'=O                           *
 *       - so p=O                                                             *
 ******************************************************************************)
 
Theorem main_thm: forall (n p : nat), n * n = double (p * p) ->  p = 0.
intros n; pattern n; apply lt_wf_ind; clear n.
intros n H p H0.
case (eq_nat_dec n 0); intros H1.
generalize H0; rewrite H1; case p; auto; intros; discriminate.
assert (H2: even n).
apply even_is_even_times_even.
apply double_even; rewrite H0; rewrite double_div2; auto.
assert (H3: even p).
apply even_is_even_times_even.
rewrite <- (double_inv (double (div2 n * div2 n)) (p * p)).
apply double_even; rewrite double_div2; auto.
rewrite main_thm_aux; auto.
assert (H4: div2 p = 0).
apply (H (div2 n)).
apply lt_div2; apply neq_O_lt; auto.
apply double_inv; apply double_inv; (repeat rewrite main_thm_aux); auto.
rewrite (even_double p); auto; rewrite H4; auto.
Qed.



(****************************************************************************** 
 *                                                                            *
 *     Coercions from nat and Z to R                                          *
 *                                                                            *
 ******************************************************************************)

Require Import Reals.
Require Import Field.
Coercion INR : nat >-> R.
Coercion IZR : Z >-> R.

(****************************************************************************** 
 *                                                                            *
 * Definition of irrational                                                   *
 *                                                                            *
 ******************************************************************************)
 
Definition irrational (x : R) : Prop :=
   forall (p : Z) (q : nat), q <> 0 ->  x <> (p / q)%R.

(******************************************************************************
 *                                                                            * 
 * Final theorem                                                              *
 *                                                                            *
 ******************************************************************************)
 
Theorem irrational_sqrt_2: irrational (sqrt 2%nat).
intros p q H H0; case H.
apply (main_thm (Zabs_nat p)).
replace (Div2.double (q * q)) with (2 * (q * q));
 [idtac | unfold Div2.double; ring].
case (eq_nat_dec (Zabs_nat p * Zabs_nat p) (2 * (q * q))); auto; intros H1.
case (not_nm_INR _ _ H1); (repeat rewrite mult_INR).
rewrite <- (sqrt_def (INR 2)); auto with real.
rewrite H0; auto with real.
assert (q <> 0%R :> R); auto with real.
field; auto with real; case p; simpl; intros; ring.
Qed.
