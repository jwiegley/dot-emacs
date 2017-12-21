(* There are regexp problems with XEmacs 21.5.28 which break this example.

   9.12.07: It turned out that the default syntax table wasn't merged 
   properly with the default, suspect bugs in derived.el.
   Patched in `proof-script.el' for now.
*)

Module Type T.

Parameter p1 : nat.
Parameter p2 : nat.
Parameter p3 : nat.
Parameter p4 : nat.
Parameter p5 : nat.
Parameter p6 : nat.
Parameter p7 : nat.
Parameter p8 : nat.

End T.
