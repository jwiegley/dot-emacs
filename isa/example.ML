(*
    Example proof script for Isabelle Proof General.

    $Id$
*)    

Goal "(A & B)-->(B & A)";
br impI 1;
br conjI 1;
be conjE 1;
ba 1;
be conjE 1;
ba 1;
qed "and_comms";
