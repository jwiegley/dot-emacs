
Module M.
  Module Type SIG.
    Parameter T:Set.
    Parameter x:T.
  End SIG.
  Module N:SIG.
    Definition T:=nat.
    Definition x:=O.
  End N.
End M.

Section toto.
Print M.
End toto.


Lemma toto : O=O.
Module N:=M.
Definition t:=M.N.T.
Trivial.
Save.


Module Type SPRYT.
  Module N.
    Definition T:=M.N.T.
    Parameter x:T.
  End N.
End SPRYT.

Module K:SPRYT:=N.  
Module K':SPRYT:=M.  

Lemma titi : O=O.
Module Type S:=SPRYT.
Module N':=M.
Trivial.
Save.


Module Type SIG.
  Definition T:Set:=M.N.T.
  Parameter x:T.

  Module N:SPRYT.
End SIG.

Module J:M.SIG:=M.N.
