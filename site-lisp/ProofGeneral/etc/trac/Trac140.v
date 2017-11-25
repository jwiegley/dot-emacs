(* Follow example shows bad behaviour in low-level regexp matching
   for output font locking.

   See http://proofgeneral.inf.ed.ac.uk/trac/ticket/140. *)

(* Note: the bad behaviour seems to be triggered when the
   pretty-printed output starts to print parameters on a
   separate line and then gets successively worse.
   p5 does this for me *)

Module Type T.

Parameter p1 : nat.
Parameter p2 : nat.
Parameter p3 : nat.
Parameter p4 : nat.
Parameter p5 : nat.

(* Parameter p6 : nat.
Parameter p7 : nat.
Parameter p8 : nat.
Parameter p9 : nat.
*)

End T. 

Time Print Module Type T. 
