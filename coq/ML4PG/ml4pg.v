Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Delimit Scope nat_scope with nat.


Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => O
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.


Require Import Coq.Lists.List.

Variable A: Type.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Set Implicit Arguments.
Open Scope nat.


(*********************************************************************************************)
(* Exported theorems *)
(*********************************************************************************************)

(*-------------------------------------------------------------------------------------------*)
(* Layer 0 : Fundamental lemmas *)
(*-------------------------------------------------------------------------------------------*)

(*1.*)
Lemma app_nil_l : forall l:list A, [] ++ l = l.
intro l.
case l.
simpl; trivial.
intros a0 l0.
simpl; trivial.
Qed.

(*2.*)
Theorem app_nil_l_shorter : forall l:list A, [] ++ l = l.
intro l.
simpl; trivial.
Qed.


(*3. alternativeApp_nil_l*)
Theorem app_nil_l_shorter' : forall l:list A, [] ++ l = l.
intro l.
simpl.  
trivial.
Qed.

(* 4 *)
Theorem app_nil_l2 : forall l: list A, l ++ [] = l.
intro l.
  induction l. 
     simpl; trivial.
    simpl.
     rewrite IHl.
       trivial.
Qed.



(* 5 *)
Theorem app_nil_l2' : forall l: list A, l ++ [] = l.
induction l. 
simpl; trivial.
simpl.
rewrite IHl. 
trivial.
Qed.

(*6.*)
Lemma mult_n_O : forall n:nat, O = n * O.
induction n.
simpl; trivial.
simpl; trivial.
Qed.

(*7.*)
Lemma mult_O_n : forall n: nat, O = O * n.
intro.
simpl.
trivial.
Qed.

(*8.*)

Lemma M15_c : forall a: nat, a = S O ->  (S O - a) * a = O.
intros.
rewrite H.
simpl.
trivial.
Qed.

(*9.*)
Lemma O_minus : forall m, O-m = O.
intro. simpl. trivial.
Qed.

(*10.*)
Lemma minus_O : forall m, m-O = m.
induction m.
  trivial.
simpl; trivial.
Qed.

(*11.*)
Lemma plus_n_O : forall n:nat, n = n + O.
induction n.
 simpl; trivial. 
simpl; trivial.
rewrite <- IHn. 
trivial.
Qed.

(*12.*)
Lemma plus_0_n : forall n:nat, n = O + n.
simpl; trivial.
Qed.

(*13.*)
Lemma addSn : forall m n, S m + n = S (m + n).
trivial. 
Qed.

(*14.*)
Lemma mulSn : forall m n, S m * n = n + m * n.
trivial. Qed.

(*15.*)
Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
induction n.
    simpl; trivial.
simpl.
intro m.
rewrite <- IHn.
trivial.
Qed.

(*16.*)
Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
induction n.
  simpl; trivial.
simpl; trivial.
Qed.

(*17.*)
Lemma aux10 : forall a, (S a - a) = S O.
induction a. 
  simpl; trivial.
simpl; trivial.
Qed.

(*18.*)
Lemma aux12 : forall n, (n * S O) = n.
induction n.
  simpl; trivial.
simpl.
rewrite IHn.
trivial.
Qed.

(*-------------------------------------------------------------------------------------------*)
(* Layer 1 : Lemmas which use layer 0 lemmas *)
(*-------------------------------------------------------------------------------------------*)

(*19.*)
Lemma addnS : forall m n, m + S n = S (m + n).
induction m. 
  trivial.
intro n.
rewrite addSn. 
rewrite addSn.
rewrite IHm.
trivial.
Qed.

(*20.*)
Lemma addnCA : forall m n k, m + (n + k) = n + (m + k).
intros m n k.
induction m.
  trivial.
rewrite plus_Sn_m. 
rewrite plus_Sn_m.
rewrite <- plus_n_Sm.
rewrite IHm. 
trivial.
Qed.



(*21.L1M*)
Lemma M1_corrected : forall l: list A, l= []
 -> tl (tl (tl l) ++  nil) = nil.
intro l.
intro H.
rewrite H.
rewrite app_nil_l2.
simpl; trivial.
Qed.

(*22. L1Mbutwithintros *)
Lemma L1Mbutwithintros : forall l: list A, l= []
 -> tl (tl (tl l) ++  nil) = nil.
intros l H.
rewrite H.
rewrite app_nil_l2.
simpl; trivial.
Qed.

(*23.*)
Lemma M2 : forall a: A, 
tl (tl (tl ([a] ++ []))) = [].
intro. 
rewrite app_nil_l2.
simpl.
trivial.
Qed.

(*24. L31Mintroal*)
Lemma M3_1: forall (a: nat) (l :list nat),  (hd O  (a :: l)) * O = O.
intro a.
intro l.
rewrite <- mult_n_O.
trivial.
Qed.

(* 25. L31M*)
Lemma L31M : forall (a: nat) (l :list nat),  (hd O  (a :: l)) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(* 26. L31Mextrasimpl *)
Lemma L31Mextrasimpl : forall (a: nat) (l :list nat),  (hd O  (a :: l)) * O = O.
intros.
simpl.
rewrite <- mult_n_O.
trivial.
Qed.

(*Many profs below follow that exact scheme with reduction of *, but it would be completely different strategies if reduction was first made in lists...*)

(*27. L32M*)
Lemma M3_2 : forall (a: nat) (l :list nat), l= [a] -> (hd O [a]) * O = O.
intro a.
intro l.
intro H.  
rewrite <- mult_n_O.
trivial.
Qed.

(*28. L32Mlessintro *)
Lemma L32Mlessintro : forall (a: nat) (l :list nat), l= [a] -> (hd O [a]) * O = O.
intro a.
intro l.
rewrite <- mult_n_O.
trivial.
Qed.


(* 29. L32Mintros *)
Lemma L32Mintros : forall (a: nat) (l :list nat), l= [a] -> (hd O [a]) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.


Definition hdn  (l:list nat) :=
    match l with
      | nil => O
      | cons x _ => x
    end.

(*30*)
Lemma M3_3: forall (a: nat) (l :list nat), l= [a] -> (hdn [a]) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*31*)
Lemma M3_4: forall a: nat, (hd O ([a] ++ [])) * O = O.
intros. 
rewrite <- mult_n_O.
trivial.
Qed.


(*32*)
Lemma M4: forall a: nat, hd O ([a] ++ [a]) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.


(*33*)
Lemma M8: forall (a b : nat), hd O [a] * O * b = O.
(* This alone does not work: intros; simpl; auto.*)
intros.
rewrite <- mult_n_O.
trivial.
Qed.


(*34*)
Lemma M16: forall a: nat, (S a - a) * O = O.
intros.  rewrite <- mult_n_O. trivial.
Qed.

(*35*)
Lemma M10: forall a: nat, a * S O * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*36*)
Lemma M13: forall a b : nat, a * hd O [b] * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*37*)
Lemma M14 : forall a: nat, (hd O [a] + O) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*38*)
Lemma M17 : forall a b: nat, (S a - b) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*39*)
Lemma M18 : forall (a b :nat), ((hd O [a]) - b) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*40*)
Lemma M18' : forall (a: list nat)(b:nat), (hd O a - b) * O = O. 
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*41*)
Lemma M19 : forall a:nat, (O - hd O [a]) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*42*)
Lemma M20 : forall a b:nat, (O - hd O [a]) * b =O.
intros. rewrite O_minus. trivial.
Qed.

(*43*)
Lemma M21 :  forall (a :nat) (b: list nat), (a - hd O b) * O = O.
intros.
rewrite <- mult_n_O.
trivial.
Qed.

(*44*)
Lemma M22 : forall a: nat, a * O * S O = O.
intros.
rewrite <- mult_n_O.
rewrite <- mult_O_n.
trivial.
Qed.

(*45*)
Lemma M24 : forall a: nat, (O - a) * S O = O.
intro.
rewrite O_minus.
rewrite <- mult_O_n.
trivial.
Qed.

(*46*)
Lemma M25 : forall a:nat,
(O - a) * S a = O.
intro.
rewrite O_minus.  
rewrite <- mult_O_n.
trivial.
Qed.

(*47*)
Lemma M26 : forall a b: nat, (O - a) * S b = O.
intros.
rewrite O_minus.
rewrite <- mult_O_n.
trivial.
Qed.

(*48*)
Lemma aux7 : forall a:nat, a-a = O.
induction a.
rewrite O_minus.
trivial.
rewrite <- IHa. 
trivial. 
Qed.


(*49*)
Lemma M31 : forall a b, hd O a * (b * O) = O.
intros. 
rewrite <- mult_n_O. 
rewrite <- mult_n_O.
trivial.
Qed.



(*50*)
Lemma M32 : forall a b, hd O a * (O - b) = O.
intros.
rewrite O_minus.  
rewrite <- mult_n_O.
trivial.
Qed.


(*51.*)
Lemma aux11 : forall n, (S O * n) = n.
induction n. 
  simpl; trivial.
simpl.
rewrite <- plus_n_O.
trivial.
Qed.

(*52*)
Lemma M36 : forall a, a * S (a * O) = a.
intro. rewrite <- mult_n_O.
rewrite aux12. trivial.
Qed.

(*53*)
Lemma M37 : forall a b, a * S (b * O) = a.
intros. rewrite <- mult_n_O.
rewrite aux12. trivial.
Qed.

(*54*)
Lemma M38 : forall a, a * S (O - a) = a.
intro. rewrite O_minus.
rewrite aux12. 
trivial.
Qed.

(*55*)
Lemma M39 : forall a, a * S (a - a) = a.
intro. rewrite aux7. rewrite aux12. trivial.
Qed.

(*56*)
Lemma M40 : forall a, a * (S a - a) = a.
intro. rewrite aux10.
rewrite aux12. trivial.
Qed.

(*57*)
Lemma M41 : forall a b, a * (O - hd O b) = O.
intros. rewrite O_minus. 
rewrite <- mult_n_O. trivial.
Qed.

(*58*)
Lemma M42 : forall a, hd O a * O + O = O.
intro. rewrite <- plus_n_O.
rewrite <- mult_n_O. trivial.
Qed.

(*59*)
Lemma M43 : forall a b, hd O a * O + b = b.
intros. 
rewrite <- mult_n_O.
simpl; trivial.
Qed.

(*60*)
Lemma M44 : forall a, a * S O + O = a.
intro. rewrite aux12.
rewrite <- plus_n_O. trivial.
Qed.

(*-------------------------------------------------------------------------------------------*)
(* Layer 2 : Lemmas which use layer 1 lemmas *)
(*-------------------------------------------------------------------------------------------*)




(*61*)
Lemma mulnS : forall n m, n * S m = n + n * m.
induction n.
   trivial. intro m.
rewrite mulSn. rewrite mulSn. rewrite addSn. rewrite addSn. rewrite addnCA.
rewrite IHn. trivial.
Qed.

(*62*)
Lemma M27 : forall a, (a - a) * S O = O.
(*intros; simpl; auto. will not work *)
intro.
rewrite aux7.
rewrite <- mult_O_n.
trivial.
Qed.

(*63*)
 (*Same proof*)
Lemma M28 : forall a, (a - a) * S a = O.
intro.
rewrite aux7.
rewrite <- mult_O_n.
trivial.
Qed.

(*64*)
Lemma M29 : forall a b, (a - a) * S b = O.
intros.
rewrite aux7.
rewrite <- mult_O_n.
trivial.
Qed.

(*65*)
Lemma M30 : forall a b, (a - a) * hd O b = O.
intros.
rewrite aux7. 
rewrite <- mult_O_n.
trivial.
Qed.

(*66*)
Lemma M33 : forall a b, hd O a * (b - b) = O.
intros.
rewrite aux7.  
rewrite <- mult_n_O.
trivial.
Qed.

(*67*)
Lemma M34 : forall a:nat, (S a - a) * a = a.
intro. rewrite aux10.
rewrite aux11. trivial.
Qed.

(*68*)
Lemma M35 : forall a b, (S a - a) * b = b.
intros. rewrite aux10.
rewrite aux11. trivial.
Qed.


(*-------------------------------------------------------------------------------------------*)
(* Layer 3 : Lemmas which use layer 1 lemmas *)
(*-------------------------------------------------------------------------------------------*)


(*69*)
Lemma M23 : forall a: nat, (a + O) * S O = a.
intro.
rewrite <- plus_n_O.
rewrite mulnS.
rewrite <- mult_n_O.
rewrite <- plus_n_O.
trivial.
Qed.

(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)


(*-------------------------------------------------------------------------------------------*)
                          (* Lemmas to look for similarities *)
(*-------------------------------------------------------------------------------------------*)



Definition hdb  (l:list bool) :=
    match l with
      | nil => false
      | cons x _ => x
    end.

(*58*)

Lemma andb_false_r : forall (a : bool) , false = andb a false.
Proof.
intros.
case a.
  simpl; trivial.
simpl; trivial.
Qed.

Lemma M3_3b: forall (a: bool) (l :list bool), l= [a] -> andb (hdb [a]) false = false.
Proof.
intros.
rewrite <- andb_false_r.







Lemma aux7_bis: forall a:nat, a-a = O.
Proof.
induction a. 
  simpl; trivial.







