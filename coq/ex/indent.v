(* First check that ".." is not considered as a command end. *)
Require Export Coq.Lists.List.
Notation "[ ]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Require Import Arith.

Record a : Type := make_a {
  aa : nat
}.

Lemma toto:nat.
Proof.
  {{
    exact 3.
  }}
Qed.

Module Y.
  Lemma L : forall x:nat , nat_iter x (A:=nat) (plus 2) 0 >= x.
  Proof with auto with arith.
    induction x;simpl;intros...
  Qed.
End Y.

Function div2 (n : nat) {struct n}: nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
  end.


Module M1.
  Module M2.
    Lemma l1: forall n:nat, n = n. 
      auto.
    Qed.
    Lemma l2: forall n:nat, n = n. 
      auto. Qed.
    Lemma l3: forall n:nat, n <= n. auto. Qed.
    (*   Lemma l4: forall n:nat, n <= n. Proof. intro. Qed. *)
    Lemma l5 : forall n:nat, n <= n.
    Proof. auto.
    Qed.
    Lemma l6: forall n:nat, n = n. 
      intros.
      Lemma l7: forall n:nat, n = n. 
        destruct n.
        BeginSubproof.
          auto.
        EndSubproof.
        BeginSubproof.
          destruct n.
          BeginSubproof.
            auto.
          EndSubproof.
          auto.
        EndSubproof.        
      Qed.
      BeginSubproof.
        destruct n.
        BeginSubproof.
          auto. EndSubproof.
        BeginSubproof. auto.
        EndSubproof.
      EndSubproof.
    Qed.
  End M2.
End M1.


Module M1'.
  Module M2'.
    Lemma l6: forall n:nat, n = n. 
      intros.
      Lemma l7: forall n:nat, n = n. 
        destruct n.
        {
          auto.
        }
        { 
          destruct n.
          {
            idtac;[
              auto
            ].
          }
          auto.
        } 
      Qed.
      {destruct n.
        {
          auto. }
        {auto. }
      }
    Qed.
  End M2'.
End M1'.


Module M1''.
  Module M2''.
    Lemma l7: forall n:nat, n = n. 
      destruct n.
      { auto. }
      { destruct n.
        { idtac; [ auto ]. }
        auto. } 
    Qed.
  End M2''.
End M1''.


Record rec:Set := { 
  fld1:nat;
  fld2:nat;
  fld3:bool
}.

Class cla {X:Set}:Set := { 
  cfld1:nat;
  cld2:nat;
  cld3:bool
}.



Module X.
  Lemma l :
    forall r:rec,
      exists r':rec,
        r'.(fld1) = r.(fld2)/\ r'.(fld2) = r.(fld1).
  Proof.
    intros r.  
    { exists 
      {|
        fld1:=r.(fld2);
        fld2:=r.(fld1);
        fld3:=false
      |}.
      split.
      {auto. }
      {auto. }
    }
  Qed.


  Lemma l2 :
    forall r:rec,
      exists r':rec,r'.(fld1) = r.(fld2) /\ r'.(fld2) = r.(fld1).
    intros r.  
    {{
        idtac;
          exists 
            {|
              fld1:=r.(fld2);
              fld2:=r.(fld1);
              fld3:=false
            |}.
    (* ltac *)
        match goal with
          | _:rec |- ?a /\ ?b => split
          | _ => fail    
        end.
        {auto. }
        {auto. }}}
  Qed.
End X.

Require Import Morphisms.
Generalizable All Variables.
Open Local Scope signature_scope.
Require Import RelationClasses.

Module foo.
  Instance: (@RewriteRelation nat) impl.
  (* No goal created *)
  Definition XX := 0.
  
  
  Instance StrictOrder_Asymmetric `(StrictOrder A R) : Asymmetric R.
  (* One goal created. Then the user MUST put "Proof." to help indentation *)
  Proof.
    firstorder.
  Qed.


  Program Fixpoint f (x:nat) {struct x} : nat :=
    match x with
      | 0 => 0
      | S y => S (f y)
    end.

  Program Instance all_iff_morphism {A : Type} :
    Proper (pointwise_relation A iff ==> iff) (@all A).

  Next Obligation.
  Proof.
    unfold pointwise_relation, all in * .
    intro.
    intros y H.    
    intuition ; specialize (H x0) ; intuition.
  Qed.
  
End foo.
