(*
    Example proof script for Coq Proof General.

    This is a legal script for coq 7.x, with
    imbricated proofs definitions.

    Replace Section by Module (>= coq-7.4).
 
    $Id$
*)

Section sect.

Goal (A,B:Prop)(A /\ B) -> (B /\ A).
 Intros A B H.
Recursive Tactic Definition  bar := Idtac.
 Elim H.
 Intros.
  Lemma foo: (A:Set)Set.
  Intro A.
  Exact A.  
  Save.
 Split.  
 Assumption.
 Assumption.
Save and_comms.
End sect.

Section newmod.
Definition type1:=Set.

Axiom A:False.
Goal (n:nat)(S n)=n.
Apply False_ind.
Exact A.
Save toto.
End newmod.

Extract Constant 

Lemma Lem : (S O)=O.
AutoRewrite [db].

Hint Rewrite [toto] in db.
AutoRewrite [db].
