(*
    Example proof script for Isabelle Proof General.

    $Id$

    Just a version of Example.ML using XSymbol
*)    

Goal "A \\<and>  B \\<longrightarrow> B \\<and>  A";
by (rtac impI 1);
by (etac conjE 1);
by (rtac conjI 1);
by (assume_tac 1);
by (assume_tac 1);
qed "and_comms";
