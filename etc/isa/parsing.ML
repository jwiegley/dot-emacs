(* Any (* nested comments *) are tricky in XEmacs (21.4.8),
   but better syntax handling in Emacs at the moment.
*)

Goal "A \\<and> B \\<longrightarrow> B \\<and> A";
by (rtac impI 1);
by (etac conjE 1);
by (rtac conjI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "and_comms";

(* Comment at the end?! *)