
Module M.
  Module Type SIG.
    Parameter T:Set.
    Parameter x:T.
  End SIG.
  Lemma toto : O=O.
  Definition t:=nat.
	 Trivial.
  Save.
  Module N:SIG.
    Definition T:=nat.
    Definition x:=O.
  End N.
  Module O:=N.
End M.

Definition t:O=O.
Trivial.
Save.


Section toto.
Print M.
End toto.

  Module N:=M.

Module R:N.SIG.
 Definition T:Set:=nat.
 Definition x:T:= O.
 Definition foo:nat:=(S O).
End R.


Module Type N'.
Module Type M'.
Declare Module K:N.SIG.
End M'.
Declare Module N''.
  Definition T:=nat.
  Definition x:=O.
End N''.

Declare Module N':M.SIG. (* no interactive def started *)
Declare Module N''':= N'. (* no interactive def started *)
Declare Module N''''. (* interactive def started *)
Parameter foo:nat.
End N''''.            (* interactive def ended *)
End N'.



Lemma titi : O=O.
Trivial.
Module Type K:=N'.
Module N''':=M.
Save.

(* Here is a bug of Coq: *)

Lemma bar:O=O.
Module Type L. (* This should not be allowed by Coq, since the End L. below fails *)
Axiom foo: O=O.
End L. (* fails --> if we go back to Module Type: unsync *)
Module I.
End I.

