(*
    Example proof script for Coq Proof General.

    This is a legal script for coq 7.x, with
    imbricated proofs definitions.

    Replace Section by Module (>= coq-7.4).
 
    $Id$
*)

Module sect.

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

Module mod.
Definition type1:=Set.
End mod.

Module Type newmod.
Definition type1:=Set.

Goal (n:nat)n=n.
Auto.
Save toto.
End newmod.

