(*
    Example proof script for Isabelle Proof General.

    $Id$
*)    

Goal "A & B --> B & A";
  by (rtac impI 1);
  by (etac conjE 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (assume_tac 1);
qed "and_comms";

Goal "(ALL x. P(x) --> Q) --> ((EX x. P(x)) --> Q)";


