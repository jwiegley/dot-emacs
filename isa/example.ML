(*
    Example proof script for Isabelle

    David Aspinall <da@dcs.ed.ac.uk>

    $Id$

*)    

goal HOL.thy
  "(A & B)-->(B & A)";
br impI 1;
br conjI 1;
be conjE 1;
ba 1;
be conjE 1;
ba 1;
qed "and_comms";

goal HOL.thy
  "(A & B)-->(B & A)";
br impI 1;
br conjI 1;
be conjE 1;
ba 1;
be conjE 1;
ba 1;
qed "and_comms";
